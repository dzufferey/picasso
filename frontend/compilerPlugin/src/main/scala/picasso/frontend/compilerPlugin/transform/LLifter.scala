package picasso.frontend.compilerPlugin.transform

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import scala.tools.nsc.util.FreshNameCreator
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin.utils._
import picasso.frontend.compilerPlugin._

class LLifter(val global: Global, val picasso: PicassoPlugin)
  extends PluginComponent with TreeUtils
{
  import global._
  import global.definitions._
  
  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List(picasso.name + ".unfold")
  
  val phaseName = picasso.name + ".llift"
  
  def newPhase(prev: Phase) = new LiftPhase(prev)

  class LiftPhase(prev: Phase) extends StdPhase(prev) {

    def apply(unit: CompilationUnit): Unit = {
      val fileNameFull = unit.source.file.name
      val fileName = if (fileNameFull endsWith ".scala") fileNameFull.substring(0, fileNameFull.length - 6) else fileNameFull
      val llifter = new Lifter(fileName, unit.fresh)
      llifter.transformUnit(unit)
      Logger("Plugin", LogInfo, "Llifter result " + unit.source.file.name + ":\n" + unit.body)
    }

  }

  /** Transforming the tree to move nested classes to package level.
   *  This needs to take care of closures and all other stuff.
   *  closure should be dealt with by having a set of reference in the class the used them.
   *  this phase needs to modify the symbols and their owners.
   *
   *  Can't we do some escape analysis ? If it does not go beyond the current scope, then fine.
   *  for this symbols have methosd "isCapturedVariable"
   *
   *  TODO the transformation should be idenpotent. this is a good sanity check.
   *
   *  TODO detecting local (in methods) variables that are captured, and pulling them at the class level
   *       this should be possible because we do not handle recursive methods (otherwise would be false).
   */
  private class Lifter(freshPrefix: String, fresh: FreshNameCreator) extends Transformer {

    def mkFreshName(pos: Position, str: String = "") = newTermName(fresh.newName(freshPrefix + "$lift" + str)) //TODO what about pos ?
    def mkFreshTypeName(pos: Position, str: String = "") = newTypeName(fresh.newName(freshPrefix + "$lift" + str)) //TODO what about pos ?

    /** Returns true if 'wrt' is not part of 'sym' owners. */
    def isFreeWRT(sym: Symbol, wrt: Symbol) = !(sym hasTransOwner wrt)
    /** isFreeWRT(_, currentOwner) */
    def isFree(sym: Symbol) = isFreeWRT(sym, currentOwner)

    lazy val collectionPackage = getModule("scala.collection")
    lazy val collectionImmutPackage = getModule("scala.collection.immutable")

    def isInlineableType(t: Type): Boolean = ( //Trick: parentheses turn off the EOL as ';'
      //TODO this is very much incomplete but will do for the moment.
      //subtypes of AnyVal are fine
      isValueClass(t.typeSymbol)
      //||(
      //     !isFunctionType(t) //actually might be inlined if does only reference immutable values ...
      //  && !(t <:< ArrayClass.tpe)
      //  &&(  !(t.typeSymbol hasTransOwner collectionPackage)
      //    || (  (t.typeSymbol hasTransOwner collectionImmutPackage)
      //       && (t.paramTypes.forall(isInlineableType(_))))
      //  )
      //)
    )

    def isInlineable(sym: Symbol) = {
      //I suppose I don't need to call asSeenFrom ...
      //or maybe do I ..., what are the arguments supposed to be ?
      //right now do nothing and let's hope for the best.
      !sym.isMutable && isInlineableType(sym.tpe)
    }


    var flattenedClasses: List[Tree] = Nil

    //list of arguments that are to be added to the constructor.
    var changedConstructors = new scala.collection.mutable.HashMap[Symbol, List[Tree]]()

    /** changes the call to some constructors outisde their class */
    class CtorArgAdderOutsideSubstituter extends Transformer {
      override def transform(tree: Tree): Tree = tree match {
        case Apply(select @ Select(New(_), nme.CONSTRUCTOR), args) if (currentClass != select.symbol.owner) && (changedConstructors contains select.symbol.owner) =>
          treeCopy.Apply(tree, select, args ::: changedConstructors(select.symbol.owner))
        case _ => super.transform(tree)
      }
    }

    class CtorArgAdderSubstituter(clazz: Type, addArgs: List[Tree]) extends Transformer {
      override def transform(tree: Tree): Tree = tree match {
        case Apply(select @ Select(New(`clazz`), nme.CONSTRUCTOR), args) =>
          treeCopy.Apply(tree, select, args ::: addArgs)
        case _ => super.transform(tree)
      }
    }
    
    /** Add parameters to the constructors.
     * @param clazz     modifies only the constructors of clazz
     * @param lhs       the symbols that are added
     * @param rhs       the right hand side of the valdefs (should just be some Select(This, $name$arg))
     */
    class AddToConstructor(clazz: Symbol, lhs: List[Symbol], rhs: List[Tree]) extends Transformer {
      
      /** To use as additional parameters.
       *  The symbols are to use only fot the arguments of the promary constructor. */
      val paramInfos: List[(Symbol, Type)] = rhs map { case select => (select.symbol, select.tpe) }

      def addToArgs(tree: Tree, additional: List[Tree]): Tree = tree match {
        case Apply(fun, args) => treeCopy.Apply(tree, fun, args ::: additional)
        case _ => Logger.logAndThrow("Plugin", LogError, "LLifter.AddToConstructor: addToArgs expect an Apply")
      }

      //TODO add to arg list: does not seem to have any effect !
      override def transform(tree: Tree): Tree = tree match {
        case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          val (vparamss2, rhs2) = if (tree.symbol.isConstructor) {
            Logger("Plugin", LogDebug, "LLifter.modifying ctor of " + clazz.name + " -> " + tree)
            //what to add:
            val valdefsSymbols = if (tree.symbol.isPrimaryConstructor) {
              paramInfos map (_._1)
            } else {
              paramInfos map { case (sym, tpe) => tree.symbol.newValueParameter(tree.pos, sym.name) setInfo tpe }
            }
            val valdefs = valdefsSymbols map (ValDef(_))
            assert(vparamss.length == 1)
            val vparamss2 = vparamss map (_ ::: valdefs)
            val rhs2 = if (!tree.symbol.isPrimaryConstructor) {
              rhs match {
                case Apply(_, _) =>
                  val additional = valdefs map (t => Ident(t.symbol))
                  addToArgs(rhs, additional)
                case Block(Nil, ctor) =>
                  val additional = valdefs map (t => Ident(t.symbol))
                  treeCopy.Block(rhs, Nil, addToArgs(ctor, additional))
                case Block(fst :: rest, something) =>
                  val additional = valdefs map (t => Ident(t.symbol))
                  treeCopy.Block(rhs, addToArgs(fst, additional) :: rest, something)
                case _ => Logger.logAndThrow("Plugin", LogError, "LLifter.AddToConstructor: not a block!")
              }
            } else {
              rhs
            }
            (vparamss2, rhs2)
          } else (vparamss, rhs)
          
          //In any case, the method may construct other object of that type: also need to change the arguments
          val newArgs = lhs map ( sym => Select(This(clazz), sym)) 
          val argAdder = new CtorArgAdderSubstituter(clazz.info, newArgs)
          val rhs3 = argAdder.transform(rhs2)
          treeCopy.DefDef(tree, mods, name, tparams, vparamss2, tpt, rhs3)

        case _ =>
          super.transform(tree)
      }
    }

    /** Add some field new field to a class.
     *  It assumes that the new params/outer referenced stuff does no require the addition of type parameters.
     *  Also assumes no companion object/factory.
     *  @param clazz        the class to modify.
     *  @param newParams    maps symbol (to replace) to new field
     *  @param outer        for reference to non value stuff. the second part are pairs to replace.
     */
    def addFields(clazz: Tree, outer: Option[(ValDef, List[(Tree,Tree)])], newParams: List[(Symbol,ValDef)]): Tree = clazz match {
      case ClassDef(modifiers, name, tparams, tmpl) => {
        //(1) replace the inner references to values and methods.
        val from = newParams map (_._1)
        val to = newParams map ( vdef => Select(This(currentClass), vdef._2.name) setType vdef._1.tpe)
        val substituer = new TreeRefSubstituter(from, to)
        val innerPartiallyModidied = substituteRef(from, to, tmpl)
        //(2) add the "outer accessor" for the maybe mutable values
        val innerModidied = outer map { case (valDef, fromTo) =>
          val outerSym = valDef.symbol
          val (from, to) = fromTo.unzip
          //val prefix = Select(This(currentClass), valDef.name) setType currentOwner.info setSymbol outerSym
          //val to = from map ( sym => {
          //  val methodSym = outerSym.newMethod(sym.name) setInfo sym.info
          //  Select(prefix, sym.name) setType sym.tpe setSymbol methodSym
          //})
          substituteTree(from, to, innerPartiallyModidied)
        } getOrElse innerPartiallyModidied
        //
        val changedTemplate = innerModidied match {
          case Template(parent, self, body) =>
            //(3) locate constructors and add new parameter
            val newSym = (outer map (o => List(o._1.symbol)) getOrElse Nil) ::: (newParams map (_._2.symbol))
            val newArgs = (outer map (o => List(o._1.rhs)) getOrElse Nil) ::: (newParams map (_._2.rhs))
            val argAdder = new AddToConstructor(currentClass, newSym, newArgs)
            val changedBody = argAdder.transformTrees(body)
            //(4) add the new fields in the body
            val newFields = (outer map (o => List(o._1)) getOrElse Nil) ::: (newParams map (_._2)) 
            //TODO do need getters for new values ?
            treeCopy.Template(innerModidied, parent, self, changedBody ::: newFields)
          case _ => Logger.logAndThrow("Plugin", LogError, "LLifter.addFields: Template is not a Template anymore ??")
        }
        treeCopy.ClassDef(clazz, modifiers, name, tparams, changedTemplate)
      }
      //TODO modules, if they do not escape, can be even removed, and their methods added to the enclosing class.
      case _ => Logger.logAndThrow("Plugin", LogError, "LLifter.addFields: does only handle ClassDef not " + clazz)
    }

    def renameClass(cls: Tree): Tree = cls match {
      case ClassDef(mods, name, tparams, tmpl)
           /*if (name.toString == nme.ANON_CLASS_NAME.toString*/ //TODO in scala 2.9 ANON_CLASS_NAME disappeared
           if (name.toString == nme.ANON_FUN_NAME.toString) =>
        val newName = mkFreshTypeName(cls.pos, name.toString)
        cls.symbol.name = newName
        treeCopy.ClassDef(cls, mods, newName, tparams, tmpl)
      case ClassDef(mods, name, tparams, tmpl)  =>
        Logger("Plugin", LogDebug, "LLift: no need to rename " + name)
        cls
      case _ => Logger.logAndThrow("Plugin", LogError, "LLifter.renameClass expect class not " + cls)
    }

    //TODO actually there should be some kind of normalization afterward since it might create some EmptyTree in classes.
    //TODO inner modules should be transformed into objects
    override def transform(tree: Tree): Tree = {
      if (tree.hasSymbol && tree.symbol.isNestedClass && tree.isInstanceOf[ClassDef]) { //TODO only classdef, not ref to class defs 
        //needs to figure out what is a free term
        //they can be collected using a FilterTreeTraverser
        Logger("Plugin", LogDebug, "transforming: " + tree.symbol + "#" + tree.symbol.id)
        //TODO this does not catch all cases ?!?
        def inParentButNotinThis(t: Tree): Boolean = (
              t.hasSymbol
          &&  t.symbol != NoSymbol
          &&  t.symbol.enclClass == currentClass //TODO when C.this.method, needs to avoid getting both method and C.this
        )
        val freeTreesFinder = new FilterTreeTraverser(inParentButNotinThis)
        freeTreesFinder.traverseTrees(tree.children)
        //TODO should get the corresponding symbol to avoid useless repretitions.
        val symbolToFreeTree = freeTreesFinder.hits groupBy (_.symbol)
        //Logger("Plugin", LogDebug, "free trees are " + symbolToFreeTree)
        val (inlineableMap, outerAccessorsMap) = symbolToFreeTree partition (t => isInlineable(t._1))
        Logger("Plugin", LogDebug, "inlineableMap: " + inlineableMap)
        Logger("Plugin", LogDebug, "outerAccessorsMap: " + outerAccessorsMap)

        //////////
        //fresh valdefs for outer accessor and inlineable values.
        //////////

        //TODO local (current scope) methods that are accessed in the methods should be allocated on the heap ?

        //outer accessor should reference classes, not symbols.
        val outerOpt: Option[(ValDef, List[(Tree,Tree)])] = if (outerAccessorsMap.isEmpty) None else {
          val tpe = currentClass.tpe
          val vname = mkFreshName(tree.pos, nme.OUTER.toString)
          val nestedClassSym = tree.symbol //this is the current class
          val vsym = nestedClassSym.newValue(vname, tree.pos) setInfo tpe
          val argSym = nestedClassSym.newValueParameter(tree.pos, mkFreshName(tree.pos, nme.OUTER.toString + "$arg")) setInfo tpe
          val rhs = Select(This(nestedClassSym), argSym) setType tpe
          val vdef = ValDef(vsym, rhs)
          val outerAccessor = Select(This(nestedClassSym), vsym) setType tpe
          //creates the parts that will replace the free trees
          val toReplace: List[(Tree,Tree)] = (for ( (sym, trees) <- outerAccessorsMap) yield {
            //sym is the symbol to be accessed (one of its parent is the enclosing class)
            //trees are the trees that have this symbol
            //in case the symbol is This
            Logger("Plugin", LogDebug, "outerAccessor for " + sym + " of " + sym.owner)
            val newRef: Tree = 
              if (sym == currentClass) outerAccessor
              else {
                assert(sym.owner == currentClass)
                Select(outerAccessor, sym) setType sym.info
              }
            trees.map(t => (t, newRef)).toList
          }).toList.flatten
          Some((vdef, toReplace))
        }
        val params: Map[Symbol,(ValDef, Seq[Tree])] = inlineableMap.map{ case (sym, trees) =>
          val tpe = sym.tpe
          val vname = mkFreshName(tree.pos, "$closure")
          val vsym = currentOwner.newValue(vname, tree.pos) setInfo sym.tpe
          val argSym = currentOwner.newValueParameter(tree.pos, mkFreshName(tree.pos, "$closure$arg")) setInfo tpe
          val rhs = Select(This(currentClass), argSym) setType tpe
          val vdef = ValDef(vsym, rhs)
          (sym, (vdef, trees))
        }

        //changedConstructors: first outer, then params
        val newArgs = (outerOpt map (_ => This(currentClass) setType currentClass.tpe)).toList ::: (params.keys map (s => Select(This(currentClass) setType currentClass.tpe, s) setType s.tpe)).toList
        changedConstructors += ((tree.symbol, newArgs))

        //TODO
        assert(params.isEmpty)
        //val tree2 = addFields(tree, outerOpt, params)
        val tree2 = addFields(tree, outerOpt, Nil)
        val tree3 = renameClass(tree2)
        val afterRecursion = super.transform(tree3)
        flattenedClasses = afterRecursion :: flattenedClasses
        EmptyTree

      } else {
        //this would flatten recursively
        val tree2 = super.transform(tree)
        tree2 match {
          //add extracted classes to the package
          case pck @ PackageDef(pid0 , stats0 ) if (!flattenedClasses.isEmpty) =>
            //change the owner of the classes to the package
            for (clazz <- flattenedClasses) {
              val chown = new ChangeOwnerTraverser(clazz.symbol.owner, pck.symbol)
              chown.traverse(clazz)
            }
            val stats1 = stats0 ::: flattenedClasses
            val pkg2 = treeCopy.PackageDef(tree2, pid0, stats1)
            val outsideCtor = new CtorArgAdderOutsideSubstituter
            //modifies the constructors when needed (see changedConstructors)
            val tree3 = outsideCtor.transform(pkg2)
            //rename the flattenedClasses references
            val renamedSymbols = flattenedClasses map (_.symbol)
            flattenedClasses = Nil
            substSymbol(renamedSymbols, renamedSymbols, tree3)
          case t => t
        }
      }
    }

  }

}
