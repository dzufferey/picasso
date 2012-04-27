package picasso.ast

import picasso.math.hol.Literal

sealed abstract class Pattern {
  def toStringRaw: String
  def ids: Set[ID]
}
case class PatternLit[T](l: Literal[T]) extends Pattern {
  def toStringRaw = "PatternLit("+l+")"
  override def toString = l.toString
  def ids = Set.empty[ID]
}
case class PatternTuple(lst: List[Pattern]) extends Pattern {
  def toStringRaw = lst.map(_.toStringRaw).mkString("PatternTuple(", ", " ,")")
  override def toString = lst.mkString("(", ", " ,")")
  def ids = (Set.empty[ID] /: lst)(_ ++ _.ids)
}
case class Case(uid: String, args: List[Pattern]) extends Pattern {
  def toStringRaw = "Case(" + uid + args.map(_.toStringRaw).mkString(", ", ", ", ")")
  override def toString = uid + args.mkString("(", ", " ,")")
  def ids = (Set.empty[ID] /: args)(_ ++ _.ids)
}
case object Wildcard extends Pattern {
  def toStringRaw = "Wildcard"
  override def toString = "_"
  def ids = Set.empty[ID]
}
case class Binding(v: ID, p: Pattern) extends Pattern {
  def toStringRaw = "Binding("+v.toStringRaw+" @ "+p.toStringRaw+")"
  override def toString = p match {
    case Wildcard => v.toString
    case _ => v + " @ " + p
  }
  def ids = p.ids + v
}

object Ident {
  //def apply(lid: String) = Binding(Variable(lid), Wildcard)
  def apply(v: ID) = Binding(v, Wildcard)
  def unapply(p: Pattern): Option[ID] = p match {
    case Binding(v, Wildcard) => Some(v)
    case _ => None
  }
}
