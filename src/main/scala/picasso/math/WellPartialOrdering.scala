package picasso.math

import scala.math.Ordering._

/** Like a partial ordering but well-founded. */
trait WellPartialOrdering[A] extends PartialOrdering[A] {
  //to implement this trait, needs to override:
  // tryCompare: (A,A) => Option[Int]
  // lteq: (A,A) => Boolean
}

trait WellOrdering[A] extends Ordering[A] with WellPartialOrdering[A] {
}

object WellPartialOrdering {
  /** canonical well-partial ordering on the Cartesian product of well-partially ordered types <code>T1</code> and <code>T2</code> */
  implicit def Tuple2[T1, T2](implicit ord1: WellPartialOrdering[T1], ord2: WellOrdering[T2]): WellPartialOrdering[(T1, T2)] = 
    new WellPartialOrdering[(T1, T2)]{
      def tryCompare(x: (T1, T2), y: (T1, T2)): Option[Int] = {
	ord1.tryCompare(x._1, y._1) match {
          case None => None
          case Some(v1) => {
            val v2 = ord2.compare(x._2, y._2) 
            if (v1 == v2) Some(v1) else None
          }
        }
      }
      def lteq(x: (T1, T2), y: (T1, T2)): Boolean = {
        ord1.lteq(x._1, y._1) && ord2.lteq(x._2, y._2)
      }
    }

  implicit def wellPartiallyOrdered[T <% WellPartiallyOrdered[T]]: WellPartialOrdering[T] = 
    new WellPartialOrdering[T] {
      def tryCompare(x: T, y: T): Option[Int] = x tryCompareTo y
      def lteq(x: T, y: T): Boolean = x <= y
    }

  /** trivial well-partial ordering on a finite type <code>T</code> */
  def IdentityWPO[T /* <: Finite */]: WellPartialOrdering[T] =
    new WellPartialOrdering[T]{
      def tryCompare(x: T, y: T): Option[Int] = {
        if (x == y) Some(0) else None
      }

      def lteq(x: T, y: T) = x == y
    }
}

object WellOrdering {
  /** well-ordering on the natural numbers */
  implicit object NatOrdering extends IntOrdering with WellOrdering[Int] {}
}
