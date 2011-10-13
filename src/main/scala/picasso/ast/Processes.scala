package picasso.ast

sealed abstract class Process {
  def toStringRaw: String
}
case class Block(stmts: List[Process]) extends Process {
  def toStringRaw = stmts.map(_.toStringRaw).mkString("Block(", ", ", ")")
  override def toString = stmts.mkString("{","; ","}") 
}
case class Affect(id: ID, value: Expression) extends Process {
  def toStringRaw = "Affect("+id.toStringRaw+","+value.toStringRaw+")"
  override def toString = id + " := " + value
}
case class Expr(e: Expression) extends Process {
  def toStringRaw = "Expr("+e.toStringRaw+")"
  override def toString = e.toString
}
case class Send(dest: Expression, content: Expression) extends Process {
  def toStringRaw = "Send("+dest.toStringRaw+","+content.toStringRaw+")"
  override def toString = dest + "!" + content
}
case class Receive(src: Expression, pat: Pattern) extends Process {
  def toStringRaw = "Receive("+src.toStringRaw+","+pat.toStringRaw+")"
  override def toString = src + "?" + pat
}

object Skip {
  def apply() = Expr(Unit())
  def unapply(p: Process): Boolean = p match {
    case Expr(Unit()) => true
    case _ => false
  }
}

object Zero {
  def apply() = Block(Nil)
  def unapply(p: Process): Boolean = p match {
    case Block(Nil) => true
    case _ => false
  }
}

object Assume {
  def apply(e: Expression) = Expr(Application("assume", List(e)))
  def unapply(p: Process): Option[Expression] = p match {
    case Expr(Application("assume", List(e))) => Some(e)
    case _ => None
  }
}

object Assert {
  def apply(e: Expression) = Expr(Application("assert", List(e)))
  def unapply(p: Process): Option[Expression] = p match {
    case Expr(Application("assert", List(e))) => Some(e)
    case _ => None
  }
}

object Havoc {
  def apply(ids: List[ID]) = Expr(Application("havoc", ids))
  def unapply(p: Process): Option[List[ID]] = p match {
    case Expr(Application("havoc", lst)) =>
      if (lst forall (_ match { case ID(_) => true case _ => false})) {
        val ids: List[ID] = lst map (_ match { case id @ ID(_) => id case _ => sys.error("should be unreachable!!")})
        Some(ids)
      } else {
        None
      }
    case _ => None
  }
}
