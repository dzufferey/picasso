package picasso.frontend.compilerPlugin

import scala.collection.mutable.{HashMap, ListBuffer, Stack}
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.utils.Namer
import picasso.graph.Automaton
import picasso.graph.{GT, DiGraph}


//Intermediate representation for scala code.

trait RawScala {
  self: AnalysisUniverse =>
  
  import global._
  import global.definitions._

  //TODO unify the location business

  type SingleLocation = (String, Position)
  //when many locations are put into one abstract loc
  class Loc(val id: String, locs: List[SingleLocation]) {
    override def toString = id
    def toStringFull = "TODO: intervals of lines in src files"
  }
  //TODO refienement loc ?

  def locShortString(loc: SingleLocation) = loc._1
  def locLongString(loc: SingleLocation) = "(" + loc._1 + ", " + loc._2 + ")"

  
  /** The type of graphs to use RawScala.scala (full CFA, i.e. without predicate abstraction) */
  type RScala = GT {
    type V = SingleLocation
    type VL = Unit
    type EL = Tree //TermTree would be nice, but CaseDef are not in subtype of TermTree
  }

  //This is actually for both classes and modules
  class Class(impl: ImplDef) {

    override def toString = symbol.toString

    val symbol = impl.symbol

    val definition = impl

    val tparams: List[TypeDef] = impl match {
      case ClassDef(_, _, tparams, _) => tparams
      case ModuleDef(_, _, _) => Nil
    }

    val template: Template = impl match {
      case ClassDef(mods, name, tparams, tmpl) => tmpl
      case ModuleDef(mods, name, tmpl) => tmpl
    }

    val methods: Map[Symbol, Method] = {
      (Map.empty[Symbol, Method] /: template.body){
        case (acc, dd @ DefDef(_,_,_,_,_,_)) => acc + (dd.symbol -> new Method(dd)) 
        case (acc, _) => acc
      }
    }

    val store: Map[Symbol, Value] = {
      (Map.empty[Symbol, Value] /: template.body){
        case (acc, vd @ ValDef(_,_,_,_)) => acc + (vd.symbol -> new Value(vd)) 
        case (acc, _) => acc
      }
    }

    val namedMembers: Map[Name, List[Symbol]] = {//multiple symbols due to overloading.
      val keys = methods.keys ++ store.keys
      (Map.empty[Name, List[Symbol]] /: keys)( (acc, k) => {
        acc + Pair(k.name, k :: ((acc.get(k.name) getOrElse Nil)))
      })
    }

    val parents: List[Symbol] = impl.impl.parents map (_.symbol) 

    def predicates = store.values.filter(_.isPredicate)

    def primaryCtor = methods.find{case (k, _) => k.isPrimaryConstructor}.get._2

    /** Call graph of methods of this class calling methods of this class */
    val selfCallGraph: DiGraph[SymGT] = {
      val called = methods mapValues (_.calledMethods)
      val edges = called.flatMap[(Symbol, Symbol), Iterable[(Symbol, Symbol)]]{ case (k,vs) => vs.toList.map((k,_))}
      DiGraph[SymGT](edges)
    }

    /** Reflexive and transitive closure of selfCallGraph */
    val selfReflTransCallGraph: DiGraph[SymGT] = selfCallGraph.reflexiveTransitiveClosure

    /** The values (of that class) that might be (transitively) affected by a call to method. */
    def affectedValues(method: Symbol): Set[Symbol] = {
      val callees = selfReflTransCallGraph(method)
      val affected = callees flatMap (methods(_).affectedValues)
      affected
    }

    /** Pull the method local variables up to the class level.
     *  This is only safe to do when there is no real recursion (tail calls are fine).
     *  TODO this should be directly done on the Tree rather than on the Class
     */
    def makeLocalVariablesTopLevel: Class = {
      val (methods2, tmpAddValues) = methods.values.map(_.extractLocalVariables).unzip
      val valuesToAdd = tmpAddValues.flatten.map(_.definition).toList
      //Logger("Plugin", LogDebug, "makeLocalVariablesTopLevel: valuesToAdd " + valuesToAdd)
      val methods2Code = methods2.map(_.definition).toList
      val storeCode = store.values.map(_.definition).toList
      val body2: List[Tree] = methods2Code ::: storeCode::: valuesToAdd
      val newTemplate = treeCopy.Template(template, template.parents, template.self, body2)
      val newClass = impl match {
        case ClassDef(mods, name, tparams, _) => treeCopy.ClassDef(impl, mods, name, tparams, newTemplate)
        case ModuleDef(mods, name, _) => treeCopy.ModuleDef(impl, mods, name, newTemplate)
      }
      new Class(newClass)
    }

    /** Can this class be safely nested ? (e.g. is anonymous function) */
    def isNestable = symbol.isAnonymousClass || symbol.isAnonymousFunction

    //TODO problem with funcall and apply which is not added: so when there are multiple fct, no possible to know which is what.
    //TODO maybe by renaming the methods (including constructor, I should be able to get it back)
    
    /** Take one class which is only referenced once in the class and merge it into the current class.
     *  For the moment, it is designed to handle anonymous functions.
     *  `New` elements of the outer class are transformed into `Select.<init>`
     *  TODO this should be directly done on the Tree rather than on the Class
     */
    def flattenNestedClass(nested: Class): Class = {
      Logger("Plugin", LogDebug, "Merging "+nested+" into "+this)
      //TODO check that there is no more than one instance of the class that is live at a given point.
      //TODO also check that the class cannot escape.
      //TODO ckeck that there is no other reference to this class somewhere in the code
      //TODO there is a few part that requires some renaming (not urgent since symbols are used)
      val thisFlat = this.makeLocalVariablesTopLevel
      val nestedFlat = nested.makeLocalVariablesTopLevel
      val thisMethods = thisFlat.methods.values.map(_.definition).map(newAsSelect(List(nested.symbol), _)).toList
      val nestedMethods = nestedFlat.methods.values.map(_.definition).toList
      val thisStore = thisFlat.store.values.map(_.definition).toList
      val nestedStore = nestedFlat.store.values.map(_.definition).toList
      //change owner to make everthing part of this class
      val newBodyOldOwner = thisMethods ::: nestedMethods ::: thisStore ::: nestedStore
      val newBody = newBodyOldOwner.map(substSymbol(List(nested.symbol), List(symbol), _))
      //this completely drops the things comming for the nested part. TODO merge the 'headers' ?
      val newTemplate = treeCopy.Template(template, template.parents, template.self, newBody)
      val newClass = impl match {
        case ClassDef(mods, name, tparams, _) => treeCopy.ClassDef(impl, mods, name, tparams, newTemplate)
        case ModuleDef(mods, name, _) => treeCopy.ModuleDef(impl, mods, name, newTemplate)
      }
      new Class(newClass)
    }

    def findNewTrees: List[Tree] = findInTree(impl, {case Apply(New(_), _) => true; case _ => false}) //is it possible to have new without apply ?

    def findObjectCreated: List[Symbol] = {
      val created = findInTree(impl, {case New(_) => true; case _ => false})
      val types = created map {case New(tpt) => tpt.tpe; case _ => NoType} //NoType should not occur
      types map (_.typeSymbol) //or termSymbol ?
    }

    def nest: Class = {
      val created = findObjectCreated
      Logger("Plugin", LogDebug, this + " creates: " + created.mkString("",", ",""))
      val nestable = created.filter(classes.get(_).map(_.isNestable).getOrElse(false))
      Logger("Plugin", LogDebug, this + " -> nestable: " + nestable.mkString("",", ",""))
      val toNest = nestable.map(classes(_))
      val toNest2 = toNest map (_.nest) //assumes the nesting is not reccursive (otherwise loop forever)
      for (clazz <- toNest2) classes -= clazz.symbol //remove the class that get nested
      val result = (this /: toNest2)(_.flattenNestedClass(_))
      classes += (result.symbol -> result)
      result
    }

  }


  object Class {

    def apply(tree: ImplDef) = tree match {
      case cd @ ClassDef(mods, name, tparams, impl) => new Class(cd)
      case md @ ModuleDef(mods, name, impl) => new Class(md)
    }

  }

  class Method(code: DefDef) {

    //TODO pre and post condition ??

    val symbol = code.symbol
    val tpe = symbol.tpe
    def definition = code
    def inClass = symbol.enclClass

    //when a methods override another, it is usefull to know where is the fisrt definition of the method
    def earliestSymbol: Symbol = earliestMethod(symbol)

    val vparams: List[ValDef] = {
      assert(code.vparamss.length <= 1)
      code.vparamss.headOption getOrElse Nil
    }
    val tparams: List[TypeDef] = code.tparams
    val returnType: Type = code.tpt.tpe
    
    val returnSym =
      if (returnType =:= UnitClass.tpe || returnType =:= NothingClass.tpe || symbol.isConstructor) NoSymbol
      else symbol.newValue(code.name + "$return", code.pos) setInfo returnType


    /** returns the local variables (including arguments) */
    val localVariables: List[Symbol] = {
      val paramAndBody = (vparams ::: extractValDefs(definition.rhs)._2).map(_.symbol)
      val bindings = bindingsIn(code)
      val returnS = if (returnSym == NoSymbol) Nil else List(returnSym)
      val res = returnS ::: bindings ::: paramAndBody
      Logger("Plugin", LogDebug, "local variables in " + symbol + " are " + res.mkString("",", ",""))
      res
    }

    /** return the set of method symbols that are called within this method. */
    def calling: Set[Symbol] = {
      def methodSymbol(t: Tree) = {
        val res = t.hasSymbol && t.symbol != NoSymbol && t.symbol.isMethod
        //if (t.hasSymbol && t.symbol != NoSymbol) Console.println(t.symbol.toString + "(" + t.symbol.isMethod + ")" )
        res
      }
      findInTree(definition.rhs, methodSymbol).map(_.symbol).toSet
    }

    lazy val automaton = makeAutomaton

    //TODO facility to 'clone' the automaton (fresh nodes ?)

    //return the type params, the formals the return value and the automaton
    def makeAutomaton: Automaton[RScala] = {
      Logger("Plugin", LogDebug, "Generating automaton for " + symbol)

      val labelToLoc = new HashMap[Symbol,(RScala#V, List[Ident])]()
      def addLabel(sym: Symbol, where: RScala#V, params: List[Ident]) { labelToLoc += (sym -> (where, params)) }
      def getLabel(sym: Symbol) = labelToLoc(sym)
      
      val edges = new ListBuffer[(RScala#V, RScala#EL, RScala#V)]
      val exceptionStack = new Stack[Either[List[(Tree, RScala#V)],Tree]]

      //code to interact with the exceptionStack (catch + finally)
      def throwing(from: RScala#V, what: Tree): Unit = {
        if (exceptionStack.isEmpty) {
          val leaving = (Namer(code.name + "$uncaught"), what.pos)
          edges += ((from, Assign(Ident(errorSymbol), what), leaving))
        } else {
          val top = exceptionStack.pop
          top match {
            case left @ Left(catchers) =>
              catchers find (p => exprMatchPattern(what, p._1)) match {
                case Some((_, loc)) => edges += ((from, Assign(Ident(errorSymbol), what), loc))
                case None => throwing(from, what)
              }
            case right @ Right(EmptyTree) => throwing(from, what)
            case right @ Right(finalizer) =>
              val from2 = (Namer(code.name + "$finally"), finalizer.pos)
              buildAutomaton(from, finalizer, from2)
              throwing(from2, what)
          }
          exceptionStack push top
        }
      }

      //build the CFA
      def buildAutomaton( from: RScala#V,
                          what: Tree,
                          to: RScala#V,
                          assignTo: Option[Tree] = None //assign the value of an if to some more complex expression
                        ): Unit = what match {
        case EmptyTree => edges += ((from, EmptyTree, to))

        case LabelDef(name, params, rhs) =>
          addLabel(what.symbol, from, params)
          buildAutomaton(from, rhs, to, assignTo)

        case If(cond, thenp, elsep) =>
          //true
          val trueCase = (Namer(code.name + "$ifTrue"), thenp.pos)
          val trueGuard = ExAssume(cond)
          edges += ((from, trueGuard, trueCase))
          buildAutomaton( trueCase, thenp, to, assignTo)
          //false
          val falseCase = (Namer(code.name + "$ifFalse"), elsep.pos)
          val falseGuard = ExAssume(ExNot(cond))
          edges += ((from, falseGuard, falseCase))
          buildAutomaton( falseCase, elsep, to, assignTo)

        case Block(stats, expr) =>
          val from2 = (from /: stats)( (from, stat) => {
            val fromP = (Namer(code.name + "$block"), stat.pos)
            buildAutomaton(from, stat, fromP, None)
            fromP
          })
          buildAutomaton(from2, expr, to, assignTo)

        case Return(expr) =>
          //TODO nothing if unit + bypass normal control flow
          assert(false, "Return not yet supported")
          //edges += ((from, treeCopy.Assign(expr, returnVal, expr), to))

        case Match(selector, cases) =>
          //assert(allDisjointPatterns(cases)) TODO isDefinedAt breaks this ...
          val selectSym = getSymbolDeep(selector)
          cases foreach (buildAutomatonCaseDef(selectSym, from, _, to, assignTo))

        case Try(block, catches, finalizer) =>
          assert(allDisjointPatterns(catches))
          //assert(catches forall (c => ! treeContains(c, ( (t: Tree) => t == Throw))))
          //finally block for normal exit, i.e. no throw or catched err
          val finalizer1 = finalizer match {
            case EmptyTree => to
            case something =>
              val finalizer1 = (Namer(code.name + "$finally"), finalizer.pos)
              buildAutomaton(finalizer1, finalizer, to, None)
              finalizer1
          }
          exceptionStack push Right(finalizer)
          //for each catch creates a entry point and call recursively
          val errorLocs = catches map (casedef => {
            val catchLoc = (Namer(code.name + "$catch"), casedef.pos)
            buildAutomatonCaseDef(errorSymbol, catchLoc, casedef, finalizer1, assignTo)
            (casedef.pat, catchLoc)
          })
          exceptionStack push Left(errorLocs)
          buildAutomaton(from, block, finalizer1, assignTo)
          exceptionStack.pop
          exceptionStack.pop

        case Throw(expr) => throwing(from, expr)

        case Apply(id @ Ident(_), params) if id.symbol.isLabel =>
          val (loc, idents) = getLabel(id.symbol)
          val assigns = (idents zip params) map { case (id, rhs) => treeCopy.Assign(rhs, id, rhs) }
          val from2 = (from /: assigns)( (from, assign) => {
            val fromP = (Namer(code.name + "$label"), assign.pos)
            edges += ((from, assign, fromP))
            fromP
          })
          edges += ((from2, EmptyTree, loc))

        case Assign(lhs, rhs) => buildAutomaton(from, rhs, to, Some(lhs))
        case vd @ ValDef(_,_,_,rhs) => buildAutomaton(from, treeCopy.Assign(vd, Ident(vd.symbol), rhs), to)

        case Typed(e, _) => buildAutomaton(from, e, to, assignTo)

        case term: TermTree => 
          val edge = assignTo map (treeCopy.Assign(term, _, term)) getOrElse term
          edges += ((from, edge, to))
        
        case term: RefTree =>
          val edge = assignTo map (treeCopy.Assign(term, _, term)) getOrElse term
          edges += ((from, edge, to))

        case other => Logger.logAndThrow("Plugin", LogError, "expected term, found: " + other)
      }

      def buildAutomatonCaseDef(matching: Symbol,
                                from: RScala#V,
                                what: CaseDef,
                                to: RScala#V,
                                assignTo: Option[Tree] = None
                               ): Unit = {

        //simple version (preserve cases)
        assert(matching != null)
        val ident = Ident(matching) setType matching.tpe
        val pattern = MatchCase(ident, what.pat)
        val guard = what.guard
        val body = what.body

        val afterMatch = (Namer(code.name + "$matched"), what.pat.pos)
        edges += ((from, pattern, afterMatch))
        val afterGuard = guard match {
          case EmptyTree => afterMatch
          case t: TermTree =>
            val loc = (Namer(code.name + "$guard"), what.guard.pos)
            val trueGuard = ExAssume(what.guard)
            edges += ((afterMatch, trueGuard, loc))
            loc
          case other => Logger.logAndThrow("Plugin", LogError, "expected guard, found: " + other)
        }
        buildAutomaton(afterGuard, body, to, assignTo)

        //more complex version
        /*
        //assignmentsOfBindings
        val assigns = assignmentsOfBindings(symbol, Ident(matching), what.pat)
        val patternWoBindings = removeBindings(what.pat)
        //assumes match pattern
        val afterMatch = (Namer(code.name + "$matched"), what.pat.pos)
        val matched = ExAssume(makeMatchCase(Ident(matching), what.pat))
        edges += ((from, matched, afterMatch))
        //assumes conditions
        val afterGuard = what.guard match {
          case EmptyTree => afterMatch
          case t: TermTree =>
            val loc = (Namer(code.name + "$guard"), what.guard.pos)
            val trueGuard = ExAssume(what.guard)
            edges += ((afterMatch, trueGuard, loc))
            loc
          case other => Logger.logAndThrow("Plugin", LogError, "expected guard, found: " + other)
        }
        //body
        val newBody = makeBlock(what.body, assigns, what.body)
        buildAutomaton(afterGuard, newBody, to, assignTo)
        */
      }

      val start = (Namer(code.name + "$call"), code.pos)
      val end = (Namer(code.name + "$return"), lastStmt(code.rhs))
      val returning =
        if (returnSym == NoSymbol) None
        else Some((Ident(returnSym) setPos code.pos) setType returnType)
      Logger("Plugin", LogDebug, symbol + " returning " + returnType + "(" + returnSym + ")")
      buildAutomaton(start, code.rhs, end, returning)
      Automaton[RScala](edges, start, Set[RScala#V](end))
    }

    /** create a block of assignments for a call.
     * @param vals the values at the callsite
     * @return Block of Assign / single Assign / EmptyTree
     */
    def makeArgsAssign(vals: List[Tree]): Tree = {
      val assigns = (vparams zip vals) map {case (vd, rhs) => treeCopy.Assign(vd, Ident(vd.symbol), rhs)}
      makeBlock(EmptyTree, assigns, EmptyTree)
    }

    lazy val affectedValues: Set[Symbol] = {
      val clazz = symbol.owner
      assert(clazz.isClass)
      val values = symbolsOwnedByDirect(code.rhs, clazz) map (_.symbol) filter (_.isValue)
      Set[Symbol](values:_*)
    }

    lazy val calledMethods: Set[Symbol] = {
      val clazz = symbol.owner
      assert(clazz.isClass)
      val methods = symbolsOwnedByDirect(code.rhs, clazz) map (_.symbol) filter (_.isMethod)
      Set[Symbol](methods:_*)
    }
    
    lazy val allSymbols: Set[Symbol] = {
      val acc = new scala.collection.mutable.HashSet[Symbol]()
      acc += symbol
      acc += returnSym
      acc ++= vparams.map(_.symbol)
      for ( (_,tree,_) <- automaton.edges ) acc ++= symbolsIn(tree)
      acc.toSet //convert to the immutable version
    }


    def extractLocalVariables: (Method, List[Value]) = {
      val (method, values) = extractValDefDefs(code)
      (new Method(method), values map (new Value(_)))
    }



  }

  class Value(code: ValDef) {
    //not much to do right now, but later, predicate abstraction will get glued on top of this.

    //@Predicate annotations
    def isPredicate = self.isPredicate(code)
    lazy val pred = new GivenByUserPredicate(code)
    def predicate = {
      assert(isPredicate)
      pred
    }
    
    def definition = code
    val symbol = code.symbol

    val tpe = symbol.tpe.underlying
    val ofClass = tpe.typeConstructor
    val classSymbol = tpe.typeSymbol //TODO probably wrong
    
    val params = tpe.typeArgs
    
    val select = Select(This(symbol.owner) setType symbol.owner.info, symbol) setType symbol.info

    lazy val allSymbols: Set[Symbol] = Set(symbol)

    /** the concrete types that can be valuations of this value */
    lazy val concreteTypes: Set[Symbol] = {
      val all = subTypes(classSymbol) + classSymbol
      all filter (s => !s.isAbstractClass)
    }

  }

}
