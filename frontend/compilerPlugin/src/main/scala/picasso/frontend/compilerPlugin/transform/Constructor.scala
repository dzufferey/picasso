package picasso.frontend.compilerPlugin.transform

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.graph._
import picasso.frontend.compilerPlugin.utils._
import picasso.frontend.compilerPlugin._

class Constructor(val global: Global, val picasso: PicassoPlugin)
  extends PluginComponent with TreeUtils with Predicates
{
  import global._
  import global.definitions._

  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List(picasso.name + ".llift")
  
  val phaseName = picasso.name + ".constructor"
  
  def newPhase(prev: Phase) = new CtorPhase(prev)

  class CtorPhase(prev: Phase) extends StdPhase(prev) {

    def apply(unit: CompilationUnit): Unit = {
      val ctor = new Ctor
      ctor.transformUnit(unit)
      Logger("Plugin", LogInfo, "Constructor result " + unit.source.file.name + ":\n" + unit.body)
    }

  }

  /** Initialisation of objects:
   *  move code from values + "floating code" to constructor.
   *  TODO lazy vals must be taken care of beforehand ...
   */
  private class Ctor extends Transformer {

    private def findPrimaryConstructor(clazz: Tree): Tree = {
      val clazzSym = clazz.symbol
      def primaryCtor(tree: Tree) = {
        val sym = tree.symbol
        sym.owner == clazzSym && sym.isPrimaryConstructor
      }
      val finder = new FilterTreeTraverser(primaryCtor)
      finder.traverse(clazz)
      val candidates = finder.hits
      //a class should have exactly one primary constructor
      if (candidates.length == 1) {
        candidates(0)
      } else {
        Logger.logAndThrow("Plugin", LogError, "Constructor.findPrimaryConstructor: expected 1 primary constructor, found " + candidates.length)
      }
    }

    sealed abstract class ToMove {
      /** For paramaccessor: init from the vparams */
      def apply(vparams: List[ValDef]): List[Tree]
    }

    /** Deals with the initialisation of values and variables */
    case class ValDefInit(valdef: ValDef) extends ToMove {
      
      def apply(vparams: List[ValDef]): List[Tree] = {
        //Logger("Plugin", LogDebug, "Constructor.ValDefInit: " + valdef.name + " with " + (vparams map (_.name)))
        val lhs = Select(This(valdef.symbol.owner), valdef.symbol)
        val sym = valdef.symbol
        val rhs = if (sym.isParamAccessor) {
          assert(valdef.rhs == EmptyTree)
          val asParam = vparams find (_.name.toString.trim == valdef.name.toString.trim)//trick with the space after the name ...
          if (asParam.isEmpty) Logger("Plugin", LogWarning, "Constructor.ValDefInit: cannot find param corresponding to " + sym)
          asParam map (vd => Ident(vd.symbol)) getOrElse EmptyTree
        } else {
          valdef.rhs
        }
        val(before, rhs2) = decomposeBlock(rhs)
        before :+ treeCopy.Assign(valdef, lhs, rhs2)
      }

    }
    
    /** Code that is not part of any definition. */
    case class FloatingCode(term: TermTree) extends ToMove {
      def apply(vparams: List[ValDef]): List[Tree] = {
        val (lst, last) = decomposeBlock(term)
        lst :+ last
      }
    }

    private def partsToMove(clazz: ClassDef): (ClassDef, List[ToMove]) = {
      val body = clazz.impl.body
      val paired: List[(Tree, Option[ToMove])] = body map ( tree => tree match {
        case vd @ ValDef(mods, name, tpt, rhs) if !isPredicate(vd) => //keep predicates
          val valdef = treeCopy.ValDef(tree, mods, name, tpt, EmptyTree)
          (valdef, Some(ValDefInit(vd)))
        case t: TermTree => (EmptyTree, Some(FloatingCode(t)))
        case t => (t, None)
      })
      val (body2, toMove) = paired.unzip
      val impl2 = treeCopy.Template(clazz.impl, clazz.impl.parents, clazz.impl.self, body2 filterNot (_ == EmptyTree))
      val clazz2 = treeCopy.ClassDef(clazz, clazz.mods, clazz.name, clazz.tparams, impl2)
      (clazz2, toMove filter (_.isDefined) map (_.get))
    }


    //TODO use 'this' rather than the class
    private def removeGetterSetter(clazz: ClassDef, body: Tree): Tree = {
      val trans = {
        case Apply(t, Nil) if t.hasSymbol && (t.symbol != NoSymbol) &&
                              (t.symbol.owner == clazz.symbol) && t.symbol.isGetter => 
          val _this = This(clazz.symbol) setType clazz.symbol.info
          val value = valueOfGetterSetter(clazz.symbol, t.symbol)
          assert(value != NoSymbol)
          Select(_this, value) setType value.info
        case Apply(t, List(arg)) if t.hasSymbol && (t.symbol != NoSymbol) &&
                              (t.symbol.owner == clazz.symbol) && t.symbol.isSetter => 
          val _this = This(clazz.symbol) setType clazz.symbol.info
          val value = valueOfGetterSetter(clazz.symbol, t.symbol)
          assert(value != NoSymbol)
          val slt = Select(_this, value) setType value.info
          Assign(slt, arg)
      }: PartialFunction[Tree, Tree]
      mgt(trans, body)
    }

    private def candidateCtor(clazz: ClassDef): Option[Tree] = {
      if (clazz.symbol.isTrait) {
        //clazz.impl.body foreach (t => Console.println(t.symbol + " -> " + t.symbol.isMixinConstructor ))
        clazz.impl.body find (_.symbol.isMixinConstructor)
      } else {
        clazz.impl.body find (_.symbol.isPrimaryConstructor)
      }
    }

    /** Adds all the stuff into the Ctor.
     *  put the new code just after the super(...) call. */
    private def modifyCtor(clazz: ClassDef, toMove: Seq[ToMove]): ClassDef = {
      candidateCtor(clazz) match {
        case Some(ctor @ DefDef(mods, name, tparam, List(vparams), tpt, body)) =>
          //Does not do anykind of reordering on toMove (no dependency check)
          val pre = toMove filter {case ValDefInit(_) => true; case _ => false} flatMap (_.apply(vparams))
          val post = toMove filter {case FloatingCode(_) => true; case _ => false} flatMap (_.apply(vparams))
          //when putting stuff into the constructor, the owner should be changed ? 
          //new ChangeOwnerTraverser(oldowner, constr.symbol)(tree)
          //actually we are movingstatement rather that symbol deffinitions, so the owner should be fine.
          val body2 = body match {
            case Block(stmts, expr) => treeCopy.Block(body, stmts ::: pre.toList ::: post.toList, expr)
            case expr => treeCopy.Block(body, pre.toList ::: post.toList, expr)
          }
          //getters and setters for the class should be replace by the actual value.
          val body3 = removeGetterSetter(clazz, body2)
          val ctor2 = treeCopy.DefDef(ctor, mods, name, tparam, List(vparams), tpt, body3)
          val implContent = ctor2 :: (clazz.impl.body filterNot (_.symbol.isPrimaryConstructor))
          val impl2 = treeCopy.Template(clazz.impl, clazz.impl.parents, clazz.impl.self, implContent)
          val clazz2 = treeCopy.ClassDef(clazz, clazz.mods, clazz.name, clazz.tparams, impl2)
          clazz2
        case _ => Logger.logAndThrow("Plugin", LogError, "Constructor.modifyCtor: expected 1 primary constructor in the form of a DefDef")
      }
    }


    override def transform(tree: Tree): Tree = tree match {
      case clDef: ClassDef =>
        //first, need to fetch the main constructor, floating code, and values rhs.
        val (strippedClass, codeToMove) = partsToMove(clDef)
        //then modify the constructor
        modifyCtor(strippedClass, codeToMove)
      case _ => super.transform(tree)
    }

  }

}
