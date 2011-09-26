package picasso.frontend.compilerPlugin.transform

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import scala.tools.nsc.util.FreshNameCreator
import scala.tools.nsc.symtab.Flags._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.graph._
import picasso.frontend.compilerPlugin.utils._
import picasso.frontend.compilerPlugin._


class Link(val global: Global, val picasso: PicassoPlugin)
  extends PluginComponent with TreeUtils
{
  import global._
  import global.definitions._
  
  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List(picasso.name + ".constructor")
  
  //global FreshNameCreator, updated for each compilation unit.
  var fresh: FreshNameCreator = _
  var freshPrefix: String = ""
  def mkFreshName(pos: Position, str: String = "$link") = fresh.newName(str) //TODO what about pos ?

  val phaseName = picasso.name + ".link"
  
  def newPhase(prev: Phase) = new LinkPhase(prev)

  class LinkPhase(prev: Phase) extends StdPhase(prev) {

    var collect = true

    override def run {
      originalClasses.clear
      transformedClasses.clear
      super.run //(1) collect
      collect = false
      //transform the classes at that point.
      linkClasses
      super.run //(2) link: replace the old classes by the new ones.
    }

    def apply(unit: CompilationUnit): Unit = {
      fresh = unit.fresh
      if (collect) Collector.traverse(unit.body)
      else {
        Linker.transformUnit(unit)
        Logger("Plugin", LogInfo, "Link result " + unit.source.file.name + ":\n" + unit.body)
      }
    }

  }


  val treeCopy = new LazyTreeCopier
  val strictTreeCopy = new StrictTreeCopier

  val originalClasses = new scala.collection.mutable.HashMap[Symbol, ClassDef]
  val transformedClasses = new scala.collection.mutable.HashMap[Symbol, ClassDef]

  /*
  type SymGT = GT.ULGT {type V = Symbol}
  private def dependencyGraph: DiGraph[SymGT] = {
    val edges = originalClasses.values flatMap {
      case cd @ ClassDef(modifiers, name, tparams, Template(parents, self, body)) =>
        val sym = cd.symbol
        val dependsOn = parents map (_.symbol)
        dependsOn map (sym -> _)
    }
    DiGraph[SymGT](edges)
  }

  //find some ordering in which classes can be processed.
  private def orderClasses(graph: DiGraph[SymGT], all:Boolean = false): Seq[Symbol] = {
    Logger("Plugin", LogDebug, "class dependency graph is\n" + graph)
    val topSort = graph.topologicalSort.reverse //reverse because we want the classes that are depended on first
    val result = if (all) topSort else topSort filter (originalClasses contains _)
    Logger("Plugin", LogDebug, "linkClasses processing order: " + result.mkString("",", ",""))
    result
  }
  */

  /** Rename a method/value that is overriden and still accessed */
  def renameSuper(clazz: Symbol, toRename: ValOrDefDef): ValOrDefDef = duplicateTree(toRename) match {
    //TODO put the name of the super class when renaming:
    //TODO change the owner of the rhs
    case DefDef(mods, name, _, vparamss, _, rhs) =>
      val freshName = mkFreshName(toRename.pos, name + "$super")
      val freshSym = clazz.newMethod(freshName, toRename.pos)
      val tpe = toRename.symbol.info
      freshSym.setInfo(tpe)
      DefDef(freshSym, mods, vparamss, rhs) setType tpe
    case ValDef(mods, name, tpt, rhs) =>
      val freshName = mkFreshName(toRename.pos, name + "$super")
      val freshSym = clazz.newValue(freshName, toRename.pos)
      val tpe = toRename.symbol.info
      freshSym.setInfo(tpe)
      ValDef(freshSym, rhs) setType tpe
  }

  def codeDefinedIn(clazz: Symbol, member: Symbol): Option[ValOrDefDef] = {
    val overridden = if (member.isMethod) member.overriddenSymbol(clazz) else member
    //Console.println(clazz + " -> " + member + " as " + overridden)
    if (overridden != NoSymbol) {
      originalClasses.get(clazz).flatMap(_.impl.body.find( _.symbol == overridden ).map(_.asInstanceOf[ValOrDefDef]))
    } else None
  }

  //mixin override: the reverse of 'normal' overriding.
  // take the normal methods -> put it as the superaccessor.
  // take the the mixin methods -> put it as the usual methods.

  private class SuperCallOrderSummary(clazz: ClassDef) {

    //TODO rather than copy super methods, extract content and inline => more efficient ...

    /** map from member to call order where call order is a list of (class, member) in reverse linearisation order */
    type CallMap = Map[Symbol, List[(Symbol, Symbol)]]

    def callMapToString(cm: CallMap): String =
      cm.toList.map{ case (m, lst) => m + "->" + lst.mkString("",",","") }.mkString("","; ","")

    val symbol = clazz.symbol

    /** Decompose the baseClasses into a sequence of pairs (baseClass, mixin)
     *  as pairs of classes with their mixins (sequence in reverse linearization order).
     */
    lazy val groupedBaseAndMixin: List[(Symbol,List[Symbol])] = {
      def process(lst: List[Symbol]): List[(Symbol,List[Symbol])] = lst match {
        case x::xs =>
          assert(!x.isTrait, x + " is a trait ? " + symbol.info.baseClasses.mkString( "", ", ", ""))
          val traits = xs takeWhile (_.isTrait)
          val next = xs drop traits.length
          (x, traits) :: process(next)
        case Nil => Nil
      }
      val result = process(symbol.info.baseClasses)
      //Console.println("YYYYYYYYYYYYYYYYYYYYYYYYYYY")
      //Console.println("class : " + symbol.info)
      //Console.println("baseClasses: " + symbol.info.baseClasses)
      //Console.println("mixinClasses: " + symbol.mixinClasses)
      //Console.println("grouped: " + result)
      //Console.println("YYYYYYYYYYYYYYYYYYYYYYYYYYY")
      result
    }

    //TODO abstract method
    private def addMixin(clazz: Symbol, partial: CallMap, mixin: Symbol): CallMap = {
      def getSymbolIn(s: Symbol): Symbol = {
        val allMixins = groupedBaseAndMixin.find( _._1 == clazz ).get._2
        /*for (m <- (clazz :: allMixins)) {
          Console.println(s + " in " + m + " = " +
            m.tpe.members.contains(s) + "; " +
            s.overriddenSymbol(m) + ", " + (s == s.overriddenSymbol(m)) + "; " +
            s.overridingSymbol(m) + ", " + (s == s.overridingSymbol(m)) + "; " +
            (s.overridingSymbol(m) == s.overridingSymbol(m))
          )
        }*/
        val inLinOrderFromDef = allMixins.reverse.dropWhile( m => !m.tpe.members.contains(s) ) :+ clazz
        //Console.println("inLinOrderFromDef: " + inLinOrderFromDef)
        (s /: inLinOrderFromDef)( (s, m) => {
          val over = s.overridingSymbol(m)
          val res = if (over != NoSymbol) over else s
          //Console.println("from " + s+"#"+s.id + " to " + res+"#"+res.id)
          res
        })
      }
      //if the mixin define some of the code that overrides something, add it at the end of the list
      val ifHasCode = for (mixinDef <- originalClasses.get(mixin)) yield {
        val definedMembers = mixinDef.impl.body.map(_.symbol).filter(s => s != NoSymbol && s.isMethod && !s.isMixinConstructor && !s.isDeferred)
        //Console.println("ZZZZ adding " + mixinDef.symbol + " in " + clazz)
        //Console.println("ZZZZ adding " + definedMembers)
        val withOverridden = definedMembers.map( s => (s, getSymbolIn(s)) )
        (partial /: withOverridden)( (acc,pair) => {
          val old = acc(pair._2)
          val newer = (mixin -> pair._1) +: old
          acc + (pair._2 -> newer)
        })
      }
      ifHasCode getOrElse partial
    }
    //for method only
    private def orderCallofGroup(clazz: Symbol, mixins: List[Symbol]): CallMap = {
      val hasCode = clazz.info.members.filter(_.isMethod).map( m => (m, codeDefinedIn(clazz, m).isDefined))
      val initMap = Map(hasCode.map{ case (m, b) => if (b) (m,List(clazz -> m)) else (m,Nil)} :_*)
      //Fold right to get the good order
      (mixins :\ initMap)((mix, map) => addMixin(clazz, map, mix))
    }
    private def correspondingMemberInClass(member: Symbol): Symbol = {
      //Console.println(
      //  "looking for " + member+"#"+member.id + " in " +
      //  symbol.info.member(member.name).alternatives.map(m => m+"#"+m.id)
      //)
      val candidate = symbol.info.member(member.name).alternatives.find(s => {
        val eqTest = s == member 
        //Console.println(member+"#"+member.id + " == " + s+"#"+s.id + " -> " + eqTest)
        val overridenTest = (s.allOverriddenSymbols contains member)
        //Console.println("s.allOverriddenSymbols " + s.allOverriddenSymbols.map(s => s+"#"+s.id))
        eqTest || overridenTest
      })
      assert(candidate.isDefined)
      candidate.head
    }
    private def mergeOrderedGroups(baseMap: CallMap, superMap: CallMap): CallMap = {
      assert(! baseMap.contains(NoSymbol) )
      val superWoCtor = superMap.filterKeys(s => !s.isConstructor)//constructors have their own special methods
      val superMapBaseKeys = superWoCtor.map{ case (k,v) => (correspondingMemberInClass(k), v) }
      //TODO still not correct: fails for the actor examples
      //fails with: cases classes are mixed with Equals that redefined equals so the equals from Object is dangling
      //Console.println("baseMap: " + baseMap)
      //Console.println("superMapBaseKeys: " + superMapBaseKeys)
      //Console.println("delta keys: " + (superMapBaseKeys.keySet -- baseMap.keySet).map(s => s+"#"+s.id) )
      assert(! superMapBaseKeys.contains(NoSymbol) )
      assert(superMapBaseKeys.keySet.subsetOf(baseMap.keySet))
      baseMap.map{case (k,v) => (k, v ++ superMapBaseKeys.getOrElse(k, Nil)) }
    }

    /** Make a list of 'call order': mixin are just below their class and subclass are below the mixin of their parents. */
    def functionsCallOrder: CallMap = {
      val grouped = groupedBaseAndMixin
      Logger("Plugin", LogDebug,
        "CallOrderSummary for " + symbol +
        "\n  members: " + symbol.info.members.mkString("", ", ", "") +
        "\n  base classes: " + grouped.mkString("",", ","")
      )
      grouped.map{ case (a,b) => orderCallofGroup(a,b) }.reduceLeft(mergeOrderedGroups)
    }

    private def pCtorOrMixinCtor(t: Tree) = t.symbol.isPrimaryConstructor || t.symbol.isMixinConstructor
    private def findPCtor(s: Symbol) = originalClasses.get(s).flatMap( c => c.impl.body.find(pCtorOrMixinCtor) ).map(_.asInstanceOf[DefDef])
    private def addMixins(ctor: DefDef, mixins: List[DefDef]): DefDef = {
      val newStmts = mixins.map( mctor => Apply(Select(This(symbol), mctor.symbol), Nil) setType UnitClass.tpe )
      val (pre, post, expr) = ctor.rhs match {
        case Block(stmst, expr) => (stmst.head, stmst.tail, expr)
        case _ => Logger.logAndThrow("Plugin", LogError, "Link: ctor body is not a Block")
      }
      treeCopy.DefDef(ctor, ctor.mods, ctor.name, ctor.tparams, ctor.vparamss, ctor.tpt, makeBlock(ctor.rhs, pre :: newStmts ::: post, expr))
    }
    private def renameButFirst(groupedCode: List[(Option[DefDef],List[Option[DefDef]])]): List[(DefDef,List[DefDef])] = {
      //fisrt make sure that we have all the necessary sources //TODO warning for the missing mixins ...
      assert(groupedCode.forall{ case (a,b) => !b.exists(_.isDefined) || a.isDefined})
      val groupedCode2: List[(DefDef,List[DefDef])] = groupedCode flatMap {
        case (None, _) => Nil
        case (Some(c), lst) => List((c, lst.flatMap(_.toList)))
      }
      val renamedButWrongType = groupedCode2 match {
        case (c, lst) :: xs =>
          (c, lst.map(renameSuper(symbol, _))) :: xs.map{
            case (c, lst) => (renameSuper(symbol, c), lst.map(renameSuper(symbol, _))) }
        case Nil => Logger.logAndThrow("Plugin", LogError, "Link: ctor body is not a Block")
      }
      renamedButWrongType.map{ case (a,b) => (a.asInstanceOf[DefDef], b.map(_.asInstanceOf[DefDef])) }
    }
    private def changeFirstCall(ctor: DefDef, callee: Symbol): DefDef = ctor.rhs match {
      case b @ Block((a @ ValDef(mods, name, tpt, ap @ Apply(_, args))) :: stmts, expr) =>
        val call = treeCopy.ValDef(a, mods, name, tpt, treeCopy.Apply(ap, Select(This(symbol), callee), args))
        treeCopy.DefDef(ctor, ctor.mods, ctor.name, ctor.tparams, ctor.vparamss, ctor.tpt, makeBlock(ctor.rhs, call :: stmts, expr))
      case other => Logger.logAndThrow("Plugin", LogError, "Link: ctor body do not start with Assign(_, super.this) but " + other + "\n whole ctor is: " + ctor)
    }
    /** the ith ctor calls the (i+1)th ctor as its first statement. */
    private def stackCtors(ctors: List[DefDef]): List[DefDef] = {
      val changed = if (ctors.size == 1) Nil else ctors.sliding(2).map{
        case List(caller, callee) => changeFirstCall(caller, callee.symbol)
        case what => Logger.logAndThrow("Plugin", LogError, "Link: sliding(2) returned " + what.map(_.symbol).mkString )
      }
      changed.toList :+ ctors.last
    }
  
    /** Create a new ctor that contains the super ctors and mixin ctors
     *  @return the new primary ctor + renamed ctors from ancestors
     *  TODO This case works only when extending a class using the *primary* ctor ...
     */
    def makePrimaryCtor: (DefDef, List[DefDef]) = {
      val groupedCode = groupedBaseAndMixin.map{ case (cls, mixins) => (findPCtor(cls), mixins map findPCtor) }
      val renamedCode = renameButFirst(groupedCode)
      val ctorsOnly = renamedCode map { case (c,ms) => addMixins(c,ms) }
      val stackedCtors = stackCtors(ctorsOnly)
      (stackedCtors.head, stackedCtors.tail ::: renamedCode.flatMap(_._2))
    }

    //TODO properly handle superaccessors

    /** Checks that super call in a method are only calling super.same_method
     *  This is an arbitrary restriction, but it simlifies the code.
     *  //TODO accessors
     */
    private def superCallWithingSameMethod(stack: List[(Symbol,Symbol)]): Boolean = stack match {
      case (cls, mSym) :: (rest @ ((cls2, mSym2) :: _)) =>
        val code = codeDefinedIn(cls, mSym).get
        val superCalls = findSuperCalls(code)
        superCalls.forall( tree => tree.symbol == mSym2 ) && superCallWithingSameMethod(rest)
      case _ => true
    }

    private def changeSuper(t: Tree, next: Symbol) = t match {
      case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        val toReplace = findSuperAndAccessorCalls(rhs) //Asumes that they are calling next
        val newCall = Select(This(symbol), next)
        val newCalls = toReplace map (_ => newCall)
        substituteTree(toReplace, newCalls, t)
      case ValDef(mods, name, tpt, rhs) => Logger.logAndThrow("Plugin", LogError, "Link: changeSuper found a value ???: " + name)
      case other => Logger.logAndThrow("Plugin", LogError, "Link: changeSuper do not expect: " + other)
    }

    //from the Mixin phase of the compiler
    def methodForSuperAccessor(clazz: Symbol, mixinClass: Symbol, superAccessor: Symbol, callMap: CallMap) = {
      var bcs = clazz.info.baseClasses.dropWhile(mixinClass !=).tail
      var inClass: Symbol = NoSymbol
      var sym: Symbol = NoSymbol
      while (!bcs.isEmpty && sym == NoSymbol) {
        inClass = bcs.head
        sym = superAccessor.matchingSymbol(inClass, clazz.thisType).suchThat(sym => !sym.hasFlag(DEFERRED | BRIDGE))
        bcs = bcs.tail
      }
      assert(sym != NoSymbol, superAccessor)
      //TODO now look into the callMap: there should be an entry with (inClass, sym)
      //Console.println("XXXXXXXXXXXXXXXXXXXXXXXXX")
      //Console.println(superAccessor + " calls " + sym + " in " + inClass)
      //Console.println("XXXXXXXXXXXXXXXXXXXXXXXXX")
      (inClass, sym)
    }

    /** Take a list of method in reverse linearization order and */
    private def stackCalls(s: Symbol, stack: List[(Symbol,Symbol)]) = {
      assert(superCallWithingSameMethod(stack), "callStack: " + stack.map{case (a,b) => a+"#"+a.id+","+b+"#"+b.id }.mkString(""," -> ",""))
      //Console.println(s + " with " + stack + "; " + stack.map{ case (cls, mSym) => codeDefinedIn(cls, mSym)})
      val stack2 = if (s.isSuperAccessor) Nil else stack //superAccessors can be ignored since they will be removed.
      val definedMethods = stack2.map{ case (cls, mSym) => codeDefinedIn(cls, mSym).get }
      var needNext = true
      val methodsNeeded = definedMethods.takeWhile( code => {
        val need = needNext
        //Console.println("XXXXXXXXXXXXXXXXXXXXXXXXX")
        //Console.println("need " + code.symbol )
        //Console.println("superCalls:" + findSuperCalls(code))
        //Console.println("superAcces:" + findSuperAccessorCalls(code))
        //Console.println("superAll  :" + findSuperAndAccessorCalls(code))
        //Console.println("XXXXXXXXXXXXXXXXXXXXXXXXX")
        needNext = !findSuperAndAccessorCalls(code).isEmpty
        need
      })
      val renamed = methodsNeeded match {
        case first :: rest =>
          val firstCopy = duplicateTree(first)
          val firstOwner = firstCopy.symbol.owner
          //make sure the first metod also belongs to this class
          val classFirst = if (firstOwner != symbol) substSymbolFull(firstOwner, symbol, firstCopy) else firstCopy
          //TODO weird thing going on here
          assert(classFirst.symbol.owner == symbol, symbol + ": " + classFirst.symbol.ownerChain + " <=> " + firstCopy.symbol.ownerChain  + "\n" + first + "\n" + classFirst ) //FIXME
          val renamed = rest map (renameSuper(symbol, _))
          classFirst :: renamed
        case Nil => Nil
      }
      //assert(renamed.forall(_.symbol.owner == symbol), renamed)  //FIXME
      if (renamed.size == 0) Nil
      else if (renamed.size == 1) renamed
      else renamed.sliding(2).map{
        case List(caller, callee) => changeSuper(caller, callee.symbol)
        case what => Logger.logAndThrow("Plugin", LogError, "Link: sliding(2) returned " + what.map(_.symbol).mkString )
      }.toList :+ renamed.last
    }

    //overriding of values should be ok since the init is moved to the ctor.
    private def getValues = {
      //val values = symbol.tpe.decls.filter(s => !s.isMethod).toList
      //Console.println("XXXXXXXXXXXXXXXXXXXXXXXXX")
      //Console.println(symbol + " members: " + symbol.tpe.members)
      //Console.println(symbol + " decls: " + symbol.tpe.decls)
      //Console.println(symbol + " decls (values): " + values)
      //Console.println("XXXXXXXXXXXXXXXXXXXXXXXXX")
      val classes = symbol.tpe.baseClasses
      val allValues = classes.flatMap(_.tpe.decls.filter(s => !s.isMethod).toList)
      def findLastDef(s: Symbol) = {
        classes.find(c => codeDefinedIn(c,s).isDefined).flatMap(c => {
          val code = codeDefinedIn(c,s)
          if (c == symbol) code
          else code.map(code => substSymbol(List(c), List(symbol), duplicateTree(code)))
        })
      }
      allValues flatMap findLastDef
    }


    /** Create a new ClassDef that comprise all the super code that is needed. */
    def makeLinkedClassDef: ClassDef = {
      val (newPCtor, superCtors) = makePrimaryCtor //TODO assert this there no super call anymore (but for the top Object ctor)
      val callMap = functionsCallOrder
      Logger("Plugin", LogDebug, "CallMap for " + symbol + ": " + callMapToString(callMap) )
      //TODO make a graph of the calls: more complex case of a methods calling super.other_method
      val normalMethods = callMap filter {case (s,_) => !s.isPrimaryConstructor}
      val allMethods = normalMethods.flatMap{ case (s, stack) => stackCalls(s, stack) }.toList
      val implBody = newPCtor :: getValues ::: superCtors ::: allMethods
      //implBody.foreach(t => assert((t.symbol.owner == symbol), t + " ("+ t.symbol+") is owned by " + t.symbol.owner)) //FIXME
      val impl2 = treeCopy.Template(clazz.impl, clazz.impl.parents, clazz.impl.self, implBody)
      treeCopy.ClassDef(clazz, clazz.mods, clazz.name, clazz.tparams, impl2)
    }

  }

  private def linkClass(clazz: ClassDef) = {
    val linker = new SuperCallOrderSummary(clazz)
    linker.makeLinkedClassDef
  }

  private def linkClasses = {
    //baseClasses: start with self ends with any (reverse linearization order)
    for ((sym, clazzDef) <- originalClasses) {
      //transform only concrete classes, not trait or abstract classes.
      if (!sym.isAbstractClass && !sym.isTrait) {
        Logger("Plugin", LogDebug, "linkClasses processing: " + sym)
        transformedClasses += (sym -> linkClass(clazzDef))
      } else {
        Logger("Plugin", LogDebug, "linkClasses skipping: " + sym)
        transformedClasses += (sym -> clazzDef)
      }
    }
  }

  //In this part, all the classes accross the different compilation units are collected.
  private object Collector extends Traverser {
    override def traverse(tree: Tree): Unit = tree match {
      case cd: ClassDef => 
        assert(! (originalClasses contains cd.symbol));
        originalClasses += (cd.symbol -> cd)
      case _ => super.traverse(tree)
    }
  }

  /** getting rid of the dynamic dispatch and so ...
   *  do not aonly bring methods, but also value in the subclasses.
   *  constructors needs a special treatment: constructor actually are close to some kind of super call.
   */
  private object Linker extends Transformer {

    override def transform(tree: Tree): Tree = tree match {
      case cd: ClassDef => transformedClasses(cd.symbol)
      case _ => super.transform(tree)
    }
  }

}
