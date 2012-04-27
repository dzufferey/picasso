package picasso.utils

import scala.collection.immutable._
import scala.collection.Set

object MultiSet {
/** The empty multiset of this type */
  def empty[A] = new MultiSet[A] {
    val multiset = Map.empty[A,Int]
  }
        
/** The canonical factories for this type
 */
  def apply[A](elems: A*): MultiSet[A] = empty[A] ++ elems

  def *[A](mults: (A, Int)*): MultiSet[A] = empty[A] ++* mults
}

abstract class MultiSet[A] extends Iterable[A] {
  val multiset: Map[A,Int]

  //def empty: MultiSet[A] = new MultiSet[A]

  def apply(key: A): Int = {
    try { multiset(key) }
    catch { case _ => 0 }
  }

  def contains(key: A) : Boolean = 
    multiset(key) > 0

  override def size : Int = multiset.foldLeft(0)((acc, e) => acc + e._2)

  def toSet : Set[A] = multiset.keySet

  def + (elem: A): MultiSet[A] = {
    val self = this

    new MultiSet[A] {
      val multiset = self.multiset.updated(elem, self(elem) + 1)
    }
  }

  def +* (kv: (A, Int)): MultiSet[A] = {
    if(kv._2 < 0) throw new IllegalArgumentException("negative multiplicity")
    else if(kv._2 == 0) this
    else {
      val self = this
      new MultiSet[A] {
        val multiset = self.multiset.updated(kv._1, self(kv._1) + kv._2)
      }
    }
  }

  def intersect(that: MultiSet[A]): MultiSet[A] = {
    val commonKeys = toSet intersect that.toSet
    val commonCards = commonKeys.toSeq.map(k => (k -> math.min(this(k), that(k))))
    MultiSet*(commonCards:_*)
  }

  def - (elem: A): MultiSet[A] = this -* ((elem, 1))
  
  def -* (kv: (A, Int)): MultiSet[A] = {
    val diff = this(kv._1) - kv._2
    val m = multiset

    if(diff > 0) new MultiSet[A] {
      val multiset = m.updated(kv._1, diff)
    }
    else new MultiSet[A] {
      val multiset = m - kv._1
    }
  }

  def ++ (elems: TraversableOnce[A]): MultiSet[A] = 
    ((this: MultiSet[A]) /: elems) ((m, e) => m + e)

  def ++* (mults: TraversableOnce[(A, Int)]): MultiSet[A] = 
    ((this: MultiSet[A]) /: mults) ((m, kv) => m +* kv)

  def -- (elems: TraversableOnce[A]): MultiSet[A] = 
    ((this: MultiSet[A]) /: elems) ((m, e) => m - e)

  def --* (mults: TraversableOnce[(A, Int)]): MultiSet[A] =
    ((this: MultiSet[A]) /: mults) ((m, kv) => m -* kv)

  def iterator: Iterator[A] = 
    new Iterator[A] {
      var that: (Iterator[(A, Int)], Option[A], Int) = (multiset.iterator, None, 0)
        
      def hasNext = that match {
        case (i, _, 0) => i.hasNext
        case _ => true
      }

      def next: A = that match {
        case (i, _, 0) => {
          val in = i.next
          that = (i, Some(in._1), in._2 - 1)
          in._1
        }
        case (i, Some(e), n) => {
          that = (i, Some(e), n - 1)
          e
        }
      }
    }

  def multiplicities: Iterable[(A, Int)] = multiset
   
}
