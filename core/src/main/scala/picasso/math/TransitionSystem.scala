package picasso.math

import scala.collection.GenSeq

trait Transition[S] extends PartialFunction[S,Set[S]] {
}

abstract class TransitionSystem {
  
  type S //state
  
  //transition type
  type T <: Transition[S]
  def transitions: GenSeq[T]

  def post(s: S, t: T): Set[S] = if(t isDefinedAt s) t(s) else Set.empty[S]
  
  def post(s: S): Set[S] = {
    val applicable = transitions filter (_ isDefinedAt s)
    val successors = applicable.flatMap(_(s))
    successors.seq.toSet
  }
  
  def post(s: Set[S], t: T): Set[S] = {
    val applicable = s filter (t.isDefinedAt(_))
    val successors = applicable.flatMap(t(_))
    successors.seq.toSet
  }
  
  def post(s: Set[S]): Set[S] = (Set.empty[S] /: transitions)(_ ++ post(s,_))

}

trait Pre {
  self: TransitionSystem =>

  def pre(s: S, t: T): Set[S]
  
  def pre(s: S): Set[S] = (Set.empty[S] /: transitions)(_ ++ pre(s, _))
}

