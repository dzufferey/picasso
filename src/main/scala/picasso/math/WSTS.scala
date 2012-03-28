package picasso.math

import picasso.graph.Trace
import scala.collection.GenSeq

/** abstract view of a WSTS.
 *  The domain is embedded into the type, and the ordering implicit.
 *  The user should only have to specify the transitions.
 *  TODO put S and T as type parameters ? then WSTS can extends Traceable. seems a bad idea: makes a lot of type become explicit
 */
abstract class WSTS extends TransitionSystem {

  implicit val ordering: WellPartialOrdering[S]

  def isTraceValid(t: Trace[S,T]): Boolean = {
    t.triples forall ( t => post(t._1, t._2) exists (ordering.equiv(_, t._3)))
  }

}

//put different trait for each kind of analysis:

trait PredBasis {
  self: WSTS =>
  //for instance the pre of a reset net is easy may returns an infinite set.
  //but computing the minimal element is easy.
  //therefore it is better to have directly the pred-basis function 
  def predBasis(s: UpwardClosedSet[S], t: T): UpwardClosedSet[S]
  
  def predBasis(s: UpwardClosedSet[S]): UpwardClosedSet[S] =
    (UpwardClosedSet.empty[S] /: transitions)(_ ++ predBasis(s, _))
}
