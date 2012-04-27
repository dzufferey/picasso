package picasso.math

import scala.collection.immutable.Set
import scala.collection.parallel.immutable.ParSet
import scala.collection.IterableLike
import scala.collection.generic.Subtractable
import scala.collection.mutable.Builder

trait ClosedSet[A] extends (A => Boolean) with Iterable[A] with ClosedSetLike[A, ClosedSet[A]] {
}

//Is an immutable data structure.
//use this as a basis for both upwardclosed and downwardclosed sets
trait ClosedSetLike[A, +This <: ClosedSetLike[A, This] with ClosedSet[A]]
extends IterableLike[A, This]
    with Subtractable[A, This] {

  /** The elements that constitute the basis of the set,
   *  i.e. an antichain of etremal elements of the set. */
  def basis: ParSet[A]
  protected def fromBasis(basis: Set[A]): This
  protected def fromParBasis(basis: ParSet[A]): This 
  protected def self: This
  def empty: This
  protected def subsume(x:A, y:A): Boolean
  protected def equiv(x:A, y:A): Boolean

  def elementCovering(y: A): Option[A] = basis find (subsume(_, y))

  def contains(y: A): Boolean = elementCovering(y).isDefined
  def apply(x: A): Boolean = contains(x)

  def partOfBasis(y: A): Boolean = basis exists (equiv(_, y))

  /** Returns an iterator over the basis of the set.
   *  Since the set itself may contain infinitely many elements, depending on the domain,
   *  iterating over the whole list of element is not a good idea. */
  def iterator: Iterator[A] = basis.iterator

  /** Adds one element to the basis of the set. */
  def +(elem: A): This = if (contains(elem)) self else fromParBasis((basis filterNot (subsume(elem,_))) + elem)

  /** If the given element is part of the basis, remove it.
   *  If it is not contained then do nothing.
   *  If it is contained in the set, but not part of the basis, then fails */
  def -(elem: A): This =
    if (basis exists (equiv(_, elem))) {
      fromParBasis(basis filterNot (subsume(elem, _)))
    } else if (!contains(elem)) {
      if (basis exists (subsume(elem, _)))
        sys.error("UpwardClosedSet (+) : cannot remove element smaller than basis.")
      else self
    } else sys.error("UpwardClosedSet (-) : cannot remove non-basis element.")

  override def equals(that: Any): Boolean = that match {
    case that: ClosedSet[_] => //TODO better too many thing extends Iterable
      (self eq that) ||
      ((that canEqual self) &&
      (self.size == that.size) &&
      (try that.asInstanceOf[This] forall (partOfBasis(_)) //TODO do we need the symmetric ?
       catch { case ex: ClassCastException => false }))
    case _ =>
      false
  }

  protected val toStringPrefix: String
  override def toString = basis.mkString(toStringPrefix+"{",";","}")
  
  /** takes the union of two sets (types are bad due to contravariance) */
  def ++(that: Iterable[A]): This = (self /: that)(_ + _)
  
  def subsetOf(that: ClosedSet[A]): Boolean = this forall (that(_))
    
  override protected[this] def newBuilder: Builder[A, This] = new ClosedSetBuilder(empty)
}

class ClosedSetBuilder[A, Coll <: ClosedSet[A] with ClosedSetLike[A, Coll]](empty: Coll) extends Builder[A, Coll] {
  protected var elems: Coll = empty
  def +=(x: A): this.type = { elems = elems + x; this }
  def clear() { elems = empty }
  def result: Coll = elems
}

class UpwardClosedSet[A](basisElements: ParSet[A])(implicit ordering: WellPartialOrdering[A]) extends ClosedSet[A] with ClosedSetLike[A, UpwardClosedSet[A]] {
  def basis: ParSet[A] = basisElements
  protected def self: UpwardClosedSet[A] = this
  protected def fromBasis(basis: Set[A]): UpwardClosedSet[A] = new UpwardClosedSet(basis.par)
  protected def fromParBasis(basis: ParSet[A]): UpwardClosedSet[A] = new UpwardClosedSet(basis)
  protected def subsume(x:A, y:A): Boolean = ordering.lteq(x,y)
  protected def equiv(x:A, y:A): Boolean = ordering.equiv(x,y)
  override def canEqual(that: Any): Boolean = that match {
    case _: UpwardClosedSet[_] => true
    case _ => false
  }
  override protected val toStringPrefix = "up"
  def empty: UpwardClosedSet[A] = new UpwardClosedSet[A](ParSet.empty[A])
}

object UpwardClosedSet {
  def fromBasis[A](elems: Set[A])(implicit ordering: WellPartialOrdering[A]) = empty[A].fromBasis(elems)
  def fromParBasis[A](elems: ParSet[A])(implicit ordering: WellPartialOrdering[A]) = empty[A].fromParBasis(elems)
  def apply[A](elems: A*)(implicit ordering: WellPartialOrdering[A]) = (empty[A] /: elems)(_ + _)
  def apply[A](elems: Iterable[A])(implicit ordering: WellPartialOrdering[A]) = (empty[A] /: elems)(_ + _)
  def empty[A](implicit ordering: WellPartialOrdering[A]) = new UpwardClosedSet[A](ParSet.empty[A])
}

class DownwardClosedSet[A](basisElements: ParSet[A])(implicit ordering: WellPartialOrdering[A]) extends ClosedSet[A] with ClosedSetLike[A, DownwardClosedSet[A]] {
  def basis: ParSet[A] = basisElements
  protected def self: DownwardClosedSet[A] = this
  protected def fromBasis(basis: Set[A]): DownwardClosedSet[A] = new DownwardClosedSet(basis.par)
  protected def fromParBasis(basis: ParSet[A]): DownwardClosedSet[A] = new DownwardClosedSet(basis)
  protected def subsume(x:A, y:A): Boolean = ordering.gteq(x,y)
  protected def equiv(x:A, y:A): Boolean = ordering.equiv(x,y)
  override def canEqual(that: Any): Boolean = that match {
    case _: DownwardClosedSet[_] => true
    case _ => false
  }
  override protected val toStringPrefix = "down"
  def empty: DownwardClosedSet[A] = new DownwardClosedSet[A](ParSet.empty[A])
}

object DownwardClosedSet {
  def fromBasis[A](elems: Set[A])(implicit ordering: WellPartialOrdering[A]) = empty[A].fromBasis(elems)
  def fromParBasis[A](elems: ParSet[A])(implicit ordering: WellPartialOrdering[A]) = empty[A].fromParBasis(elems)
  def apply[A](elems: A*)(implicit ordering: WellPartialOrdering[A]) = (empty[A] /: elems)(_ + _)
  def apply[A](elems: Iterable[A])(implicit ordering: WellPartialOrdering[A]) = (empty[A] /: elems)(_ + _)
  def empty[A](implicit ordering: WellPartialOrdering[A]) = new DownwardClosedSet[A](ParSet.empty[A])
}
