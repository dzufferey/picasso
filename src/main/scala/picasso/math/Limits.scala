package picasso.math

import scala.collection.immutable.Set
import picasso.graph.Trace
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}

//(W)ADL: (weak) adequate domain of limit.
// how to define an ideal ?
// this relies on mathematical properties taht cannot be enforce by the type system.
// Therefore the hypothesis and invariants should be made clear in the text ...
/* Summary:
an ADL for set X is a triple (L,\predeq,\gamma) where L is a set of Limits (dijoint from X):
(L1) \gamma: L \cup X -> 2^X such that \gamma(z) is downwards closed for all y in L \cup X,
     and \gamma(x) = \downarraow x for all x in X;
(L2) there is \top s.t. \gamma(\top) = X;
(L3) z \predeq z' <=> \gamma(z) \subseteq \gamma(z');
(L4) for any downward-closed subset D of X, there is a finite subset E of L \cup X s,t \biccup_{e in E} \gamma(e) = D.
a WADL satisfies only (L1), (l2), and (l4).

Alternative view (Finkel, Goubault-Larrecq):

a Notherian space is a topological space where:
every closed subsets satisfy the descending chain condition,
every open subsets satisfy the ascending chain condition,
every subset is compact (...).
Alexandorff topoloy is a topological space in which the intersection of any family of open sets is open.
a dcposet set X is Notherian with its Alexandorff topoloy.
Scott topology on X has as open all upward closed subset U s.t. every directed family of that has a lub in X intersectd U (some member of the family is in U).
the closure of a subset of X is the smallest closed subset containg X.
a closed subset F is irreducible iff F is non-empty and F \subseteq F_1 \cup F_2 then F \subseteq F_1 or F subseteq F_2.
a space X is sober iff every closed subseteq F is the closure of a unique point x (F = \downarrow x)

Ideal completion: S(X), for a noetherian space X:
add all missing limis from directed families.
Also the sobrification of X.

Idl(X) is he smallest WADL on X.
*/

//define transfinite traces: for witnesses of forward algorithm
sealed abstract class TransfiniteWord[T](val word: List[T]) {

  def unfold(i: Int): Normal[T] = {
    Normal( ((0 until i) :\ (Nil: List[T]))( (_,acc) => word ::: acc))
  }
}

case class Accelerate[T](override val word: List[T]) extends TransfiniteWord[T](word) {
  override def toString = word.mkString("(",", ", ")") + "^ω"
}
case class Normal[T](override val word: List[T]) extends TransfiniteWord[T](word) {
  override def toString = word.mkString("(",", ", ")")
}

class TransfiniteTrace[S,T](start: DownwardClosedSet[S], transitions: List[(TransfiniteWord[T],DownwardClosedSet[S])]) extends Trace[DownwardClosedSet[S],TransfiniteWord[T]](start, transitions) {
  override def append(s: DownwardClosedSet[S], t: TransfiniteWord[T]) = TransfiniteTrace(start, transitions ::: List((t,s)))
  override def prepend(s: DownwardClosedSet[S], t: TransfiniteWord[T]) = TransfiniteTrace(s, (t,start) :: transitions )
  override def reverse = TransfiniteTrace(stop, triples.reverse map ( t => (t._2, t._1)))
}
object TransfiniteTrace {
  def empty[S,T](s: DownwardClosedSet[S]) = new TransfiniteTrace[S,T](s, Nil)
  def apply[S,T](start: DownwardClosedSet[S], transitions: List[(TransfiniteWord[T],DownwardClosedSet[S])]) = new TransfiniteTrace(start, transitions)
}


trait WADL {
  self: WSTS =>

  //being a WSTS means that:
  //type S
  //implicit val ordering: WellPartialOrdering[S]
  //are already defined
  //!! Assumes that the limits are part of S
  
  def postCover(s: DownwardClosedSet[S], t: T): DownwardClosedSet[S] = {
    (DownwardClosedSet.empty[S] /: s)( (acc, s) => acc ++ DownwardClosedSet[S](post(s,t)))
  }
  def postCover(s: DownwardClosedSet[S]): DownwardClosedSet[S] = (DownwardClosedSet.empty[S] /: transitions)(_ ++ postCover(s,_))

  def tryAcceleratePair(smaller: S, bigger: S): Option[S] //for acceleration a la Karp-miller

  def widening(smaller: S, bigger: S): S = {
    val opt = tryAcceleratePair(smaller, bigger)
    if (opt.isDefined) opt.get
    else Logger.logAndThrow("Limits", LogError, "widening not defined for " + smaller + " and " + bigger)
  }

  //TODO this is correct only is a Karp-Miller kind of acceleraion of possible (i.e. Petri Nets).
  def accelerate(states: DownwardClosedSet[S], transitions: List[T]): DownwardClosedSet[S] = {
    val postSet = (DownwardClosedSet.empty[S] /: states.basis)((postSet, s) => {
      val sPost = postCover(DownwardClosedSet(s), Normal(transitions))
      (postSet /: sPost)((postSet, t) => {
        val tAccel = tryAcceleratePair(s, t).getOrElse(t)
        if (ordering.lt(t, tAccel)) postSet + tAccel else postSet
      })
    })
    postSet
  }
  
  def postCover(states: DownwardClosedSet[S], transitions: TransfiniteWord[T]): DownwardClosedSet[S] = transitions match {
    case Accelerate(lst) => accelerate(states, lst)
    case Normal(lst) => (states /: lst)(postCover(_,_))
  }

  def isTraceValid(t: TransfiniteTrace[S,T]) = {
    t.triples forall ( t => t._3 subsetOf postCover(t._1, t._2))
  }


}

