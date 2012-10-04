package picasso.model.integer
  
import scala.collection.GenSeq
import picasso.graph._
import picasso.utils._
import picasso.utils.tools.armc._

/** Integer Program.
 *  Integer program are use during the termination proof of DBP.
 *  Right now their purpose is just these termination check (not safety).
 */
class Program(initPC: String, trs: GenSeq[Transition]) extends picasso.math.TransitionSystem {
  
  type S = State
  
  //transition type
  type T = Transition

  def initialPC = initPC

  def transitions: GenSeq[T] = trs

  lazy val pcs = (Set(initPC) /: trs)((acc, t) => acc + t.sourcePC + t.targetPC)

  lazy val variables: Set[Variable] = {
    trs.aggregate(Set[Variable]())(_ ++ _.variables, _ ++ _)
  }

}
