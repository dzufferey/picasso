package picasso.graph

//Warning: the iterator skips the first location
class Trace[A,B](val start: A, val transitions: List[(B,A)]) extends Iterable[(B,A)] {

  /** Returns the number of transition in the trace (#state -1) */
  def length = transitions.length

  def states = start :: transitions.map(_._2)

  def labels = transitions.map(_._1)
  
  def stop = if (transitions.length == 0) start else transitions.last._2

  override def iterator = transitions.iterator

  private def mkTriple(acc: List[(A,B,A)], current: A, rest: List[(B,A)]): List[(A,B,A)] = rest match {
    case (b,a)::xs => mkTriple( (current,b,a)::acc, a, xs)
    case Nil => acc.reverse
  }

  def extremities: (A,A) = (start, stop)

  def innerStates: List[A] = transitions.map(_._2).dropRight(1)

  def triples: List[(A,B,A)] = mkTriple(Nil, start, transitions)

  def append(s: A, t: B) = new Trace(start, transitions ::: List((t,s)))

  def concat(t: B, trc: Trace[A,B]) = new Trace(start, transitions ::: List(t -> trc.start) ::: trc.transitions)

  def prepend(s: A, t: B) = new Trace(s, (t,start) :: transitions )

  def reverse = new Trace(stop, triples.reverse map ( t => (t._2, t._1)))

  def split(at: Set[A]): List[Trace[A,B]] = {
    var acc: List[Trace[A,B]] = Nil
    var current = this
    while (!current.transitions.isEmpty) {
      val t1Prefix = current.transitions.takeWhile(elt => !at(elt._2))
      val t2Augmented = current.transitions.drop(t1Prefix.length)
      if(t2Augmented.isEmpty) {
        acc = current :: acc
        current = new Trace(current.stop, Nil)
      } else {
        acc = new Trace(current.start, t1Prefix :+ t2Augmented.head) :: acc
        current = new Trace(t2Augmented.head._2, t2Augmented.tail)
      }
    }
    assert(current.transitions.isEmpty)
    acc.reverse
  }

  def split(at: A): List[Trace[A,B]] = split(Set(at))

  override def toString = start + transitions.map( p => (p._1 + " => "+p._2)).mkString(" => ", " => ", "")

  override def equals(any: Any) = any match {
    case t: Trace[_,_] => start == t.start && transitions == t.transitions
    case _ => false
  }

}

object Trace {
  def apply[A,B](start: A, transitions: (B,A)*) = new Trace[A,B](start, transitions.toList)
}

trait Traceable[A,B] {

  def isTraceValid(t: Trace[A,B]): Boolean

}
