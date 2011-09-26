package picasso.frontend.compilerPlugin.transform

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import scala.tools.nsc.util.FreshNameCreator
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin.utils._
import picasso.frontend.compilerPlugin._

class Unfolder(val global: Global, val picasso: PicassoPlugin)
  extends PluginComponent with TreeUtils with Predicates
{
  import global._
  import global.definitions._

  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List("uncurry")
  
  val phaseName = picasso.name + ".unfold"
  
  def newPhase(prev: Phase) = new UnfoldPhase(prev)

  class UnfoldPhase(prev: Phase) extends StdPhase(prev) {

    def apply(unit: CompilationUnit): Unit = {
      Logger("Plugin", LogInfo, "Piccolo starting with " + unit.source.file.name + ":\n" + unit.body)
      val unfolder = new UnfoldExpressions(unit.source.file.name, unit.fresh)
      unfolder.transformUnit(unit)
      Logger("Plugin", LogInfo, "Unfolder result for " + unit.source.file.name + ":\n" + unit.body)
    }

  }
  
  /** Extracts nested expression to a simpler flat form.
   *  For instance:
   *    val a = f(g(b))
   *  to
   *    val tmp = g(b)
   *    val a = f(tmp)
   */
  private class UnfoldExpressions(freshPrefix: String, fresh: FreshNameCreator) extends Transformer {

    override def transform(tree: Tree): Tree = tree match {
      //TODO warning: lazy evaluation of boolean conditions
      case Apply(fun, args) => {
        val funT = transform(fun)
        val argsT = transformTrees(args)
        val (blk , finalFun) = decomposeBlock(funT) //is a select ...
        val (finalArgsBlk, finalArgsID) = argsT.map(decomposeBlock(_)).unzip
        val call = treeCopy.Apply(tree, finalFun, finalArgsID)
        if (call.tpe =:= UnitClass.tpe || call.tpe =:= NothingClass.tpe) {
          val finalBlk = blk ::: finalArgsBlk.flatten
          makeBlock(tree, finalBlk, call)
        } else {
          // fresh name + symbol: non unit case
          // at that point, it is possible to have prefix.this.type, underlying should remove it when possible
          val tpe = if (call.tpe.isStable) call.tpe.underlying else call.tpe
          val name = fresh.newName(freshPrefix + "$tmpVal")
          val sym = currentOwner.newValue(tree.pos, name).setInfo(tpe)
          val mods = NoMods
          val tpt = TypeTree(tpe)
          val _def = treeCopy.ValDef(tree, mods, sym.name, tpt, call) setType NoType setSymbol sym
          val finalBlk = blk ::: finalArgsBlk.flatten ::: List(_def)
          makeBlock(tree, finalBlk, treeCopy.Ident(tree, sym.name) setSymbol sym setType sym.tpe)
        }
        //TODO DZ: Thibaud wants an Extra 1337 -=|HACK|=-
      }
      //not like an Apply: do not change the args, only fun.
      case TypeApply(fun, args) => {
        val funT = transform(fun)
        val (blk , finalFun) = decomposeBlock(funT)
        val call = treeCopy.TypeApply(tree, finalFun, args)
        makeBlock(tree, blk, call)
      }
      case If(_, _, _) => {
        val newTree = super.transform(tree)
        newTree match {
          case If(cond, thenp, elsep) =>
            val (blk, c) = decomposeBlock(cond)
            makeBlock(newTree, blk, treeCopy.If(newTree, c, thenp, elsep))
          case _ => Logger.logAndThrow("Plugin", LogError, "UnfoldExpressions: If transformed in something else")
        }
      }
      case Select(qualifier, selector) => {
        val newTree = super.transform(tree)
        newTree match {
          case Select(qualifier, selector) => 
            //is the qualifier a Block ??
            val (blk, id) = decomposeBlock(qualifier)
            makeBlock(newTree, blk, treeCopy.Select(newTree, id, selector))
          case _ => Logger.logAndThrow("Plugin", LogError, "UnfoldExpressions: Select transformed in something else")
        }
      }
      case Assign(_, _) => 
        val newAssign = super.transform(tree)
        newAssign match {
          case Assign(lhs, rhs) => 
            val (blk, id) = decomposeBlock(rhs)
            makeBlock(newAssign, blk, treeCopy.Assign(newAssign, lhs, id))
          case _ => Logger.logAndThrow("Plugin", LogError, "UnfoldExpressions: Assign transformed in something else")
        }
      case Block(_,_) => {
        val newBlock = super.transform(tree)
        newBlock match {
          case Block(lst, expr) =>
            def decomposeBlockAndDropIdent(t: Tree): List[Tree] = {
              val (lst, expr) = decomposeBlock(t)
              expr match {
                case Ident(_) => lst
                case _ => lst ::: List(expr)
              }
            }
            makeBlock(newBlock, lst.flatMap(decomposeBlockAndDropIdent), expr)
          case _ => Logger.logAndThrow("Plugin", LogError, "UnfoldExpressions: Block transformed in something else")
        }
      }
      case CaseDef(pat, guard, body) => {
        //Do not go inside the pattern
        val newGuard = transform(guard)
        val newBody = transform(body)
        treeCopy.CaseDef(tree, pat, newGuard, newBody)
      }
      case vd @ ValDef(mods, name, tpt, rhs) => atOwner(tree.symbol) {
        if (isPredicate(vd)) {
          vd //should not unfold @Predicates
        } else {
          // if the owner is a block then put new expr in the same block
          // else keep it in nested block
          val value = transform(rhs)
          if (tree.symbol.owner.isMethod) {
            val (blk, id) = decomposeBlock(value)
            makeBlock(tree, blk, treeCopy.ValDef(tree, mods, name, tpt, id))
            //TODO this is not a well-formed Block
            //But it should be part of a bigger block ..
          } else {
            treeCopy.ValDef(tree, mods, name, tpt, value)
          }
        }
      }
      case Throw(e) =>
        val e2 = transform(e)
        val (blk, id) = decomposeBlock(e2)
        makeBlock(tree, blk, treeCopy.Throw(tree, id))
      case Typed(e,t) =>
        val e2 = transform(e)
        val (blk, id) = decomposeBlock(e2)
        makeBlock(tree, blk, treeCopy.Typed(tree, id, t))
      case _ =>
        super.transform(tree)
    }
  }

}
