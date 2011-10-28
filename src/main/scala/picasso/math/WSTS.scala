package picasso.math

import picasso.graph.Trace


trait Transition[S] extends PartialFunction[S,Set[S]] {
}

/** abstract view of a WSTS.
 *  The domain is embedded into the type, and the ordering implicit.
 *  The user should only have to specify the transitions.
 *  TODO put S and T as type parameters ? then WSTS can extends Traceable. seems a bad idea: makes a lot of type become explicit
 */
abstract class WSTS {

  type S //state
  implicit val ordering: WellPartialOrdering[S]
  
  //transition type
  type T <: Transition[S]
  def transitions: List[T] //TODO allows for parallel collections

  def post(s: S, t: T): Set[S] = if(t isDefinedAt s) t(s) else Set.empty[S]
  
  def post(s: S): Set[S] = {
    val applicable = transitions filter (_ isDefinedAt s)
    (Set.empty[S] /: applicable)(_ ++ _(s))
  }
  
  def post(s: Set[S], t: T): Set[S] = {
    val applicable = s filter (t.isDefinedAt(_))
    (Set.empty[S] /: applicable)(_ ++ t(_))
  }
  
  def post(s: Set[S]): Set[S] = (Set.empty[S] /: transitions)(_ ++ post(s,_))

  def isTraceValid(t: Trace[S,T]): Boolean = {
    t.triples forall ( t => post(t._1, t._2) exists (ordering.equiv(_, t._3)))
  }

}

//TODO put different trait for each kind of analysis.

trait Pre {
  self: WSTS =>

  def pre(s: S, t: T): Set[S]
  
  def pre(s: S): Set[S] = (Set.empty[S] /: transitions)(_ ++ pre(s, _))
}

trait PredBasis {
  self: WSTS =>
  //for instance the pre of a reset net is easy may returns an infinite set.
  //but computing the minimal element is easy.
  //therefore it is better to have directly the pred-basis function 
  def predBasis(s: UpwardClosedSet[S], t: T): UpwardClosedSet[S]
  
  def predBasis(s: UpwardClosedSet[S]): UpwardClosedSet[S] =
    (UpwardClosedSet.empty[S] /: transitions)(_ ++ predBasis(s, _))
}
