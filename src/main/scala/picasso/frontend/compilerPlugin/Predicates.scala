package picasso.frontend.compilerPlugin

import picasso.math.Boolean3Valued._
import picasso.math.hol._
import Annotations._
import scala.tools.nsc.Global
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import utils.TreeUtils


//TODO this is a wrapper around the HOL formulas and the Trees and FunCheck ?
trait Predicates {
  self: TreeUtils =>

  val global: Global

  import global._
  import global.definitions._

  lazy val annotations = getModule("picasso.frontend.compilerPlugin.Annotations") 
  lazy val predAnnotation = annotations.info.decls.find(s => s.name.toString == "Predicate").get
  //TODO is there a nicer way of getting nested classes ?

  def isPredicate(vd: ValDef) = {
    vd.symbol.annotations.exists( annot => {
      annot.atp.typeSymbol == predAnnotation
    })
  }

  abstract class Predicate {

    /** Does given symbol apprears in the predicate ? */
    def contains(s :Symbol): Boolean = containing(s)

    /** The set of symbols that are apprears in this predicate. */
    def containing: Set[Symbol]

    /** The tree (or the closest thing) that corresponds to this predicate. */
    def tree: Tree

    /** The formula corresponding to this predicate. */
    def formula: Formula

  }

  class GivenByUserPredicate(vd: ValDef) extends Predicate {

    assert(isPredicate(vd))

    private val contained = {
      val all = symbolsInvloved(vd)
      assert(all.size == 1)
      all.head._2.toSet
    }

    def containing = contained

    def tree = vd.rhs

    def formula = sys.error("TODO")

  }

  /**
  class BooleanValDefPredicate(vd: ValDef) extends Predicate {

    assert(BooleanValDefPredicate.is(vd))

    def containing = Set[Symbol](vd.symbol)

    val select = {
      Select(This(vd.symbol.owner) setType vd.symbol.owner.info, vd.symbol) setType vd.symbol.info
    }

    def tree = select

    val variable = {
      val v = Variable(vd.symbol.name + "#" + vd.symbol.id)
      v.tpe = Bool
      v
    }

    def formula = variable

  }

  object BooleanValDefPredicate {
    def is(t: Tree) = t match {
      case vd@ValDef(_,_,_,_) => vd.symbol.info == BooleanClass.tpe
      case _ => false
    }

    def apply(t: Tree) = t match {
      case vd@ValDef(_,_,_,_) if is(vd) => new BooleanValDefPredicate(vd)
      case _ => Logger.logAndThrow("Plugin", LogError, "Cannot create a BooleanValDefPredicate out of " + t)
    }

  }
  */

}
