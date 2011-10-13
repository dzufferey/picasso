package picasso.model.dbp

//introduce a more complex kind of nodes (more flexible than just PC) to accomodate more variantes of matching.
//this can be used to wrap concrete states and provides wildcard matching and alternatives
//remark: by convention when state is empty, it is a wildcard.
class DBCS[A](val states: Set[A]) extends Equals {

  def isSingle = states.size == 1
  def isWildcard = states.size == 0

  def +(other: DBCS[A]) = new DBCS[A](states ++ other.states)

  override def canEqual(x: Any): Boolean = x match {
    case x: DBCS[_] => true //TODO bad: not possible to check the inner type due to erasure.
    case _ => false
  }

  override def equals(that: Any): Boolean = that match {
    case that: DBCS[_] =>
      (this eq that) ||
      ((that canEqual this) &&
       (try this.states == that.asInstanceOf[DBCS[A]].states
        catch { case ex: ClassCastException => false }))
    case _ =>
      false
  }

  override def toString = if (isWildcard) "_" else states.mkString("","|","")

}

object DBCS {
  def apply[A](trs: Traversable[A]) = {
    assert(!trs.isEmpty)
    new DBCS[A](trs.toSet)
  }
  def apply[A](s: A) = new DBCS(Set[A](s))
  def unk[A]: DBCS[A] = new DBCS[A](Set.empty[A])
}
