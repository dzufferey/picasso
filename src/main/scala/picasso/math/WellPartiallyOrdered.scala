package picasso.math

import scala.math.Ordering._


trait WellPartiallyOrdered[A] {
  def tryCompareTo(that: A): Option[Int]
  
  def < (that: A): Boolean =
    (this tryCompareTo that) match {
      case Some(x) if x < 0 => true
      case _ => false
    }

  def > (that: A): Boolean =
    (this tryCompareTo that) match {
      case Some(x) if x > 0 => true
      case _ => false
    }

  def <= (that: A): Boolean =
    (this tryCompareTo that) match {
      case Some(x) if x <= 0 => true
      case _ => false
    }

  def >= (that: A): Boolean =
    (this tryCompareTo that) match {
      case Some(x) if x >= 0 => true
      case _ => false
    }
}
