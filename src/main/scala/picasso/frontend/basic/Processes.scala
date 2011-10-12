package picasso.frontend.basic

sealed abstract class Process extends scala.util.parsing.input.Positional
case class Block(stmts: List[Process]) extends Process
case class Affect(id: String, value: Expression) extends Process {
  override def toString = id + " := " + value
}
case class Declaration(id: String, variable: Boolean, value: Expression) extends Process {
  override def toString = (if (variable) "var " else "val ") + id + " := " + value
}
case class Expr(e: Expression) extends Process {
  override def toString = e.toString
}
case class Send(dest: Expression, content: Expression) extends Process {
  override def toString = dest + "!" + content
}
case class Receive(cases: List[(Expression,Pattern,Process)]) extends Process
case class ITE(condition: Expression, caseTrue: Process, caseFalse: Process) extends Process
case class While(condition: Expression, body: Process) extends Process
case class ForEachGeneric(id: String, set: Expression, yieldOpt: Option[(String,String)], body: Process) extends Process

object Zero {
  def apply() = Block(Nil)
  def unapply(p: Process): Option[Unit] = p match {
    case Block(Nil) => Some(())
    case Receive(Nil) => Some(())
    case Block(Receive(Nil) :: Nil) => Some(())
    case _ => None
  }
}
object ForEach {
  def apply(id: String, set: Expression, body: Process) = ForEachGeneric(id, set, None, body)
  def unapply(p: Process): Option[(String, Expression, Process)] = p match {
    case ForEachGeneric(id, set, None, body) => Some((id, set, body))
    case _ => None
  }
}

object ForEachYield {
  def apply(x: String, setX: Expression, y: String, setY: String,  body: Process) = ForEachGeneric(x, setX, Some((y, setY)), body)
  def unapply(p: Process): Option[(String, Expression, String, String, Process)] = p match {
    case ForEachGeneric(id, setId, Some((y,sy)), body) => Some((id, setId, y, sy, body))
    case _ => None
  }
}

object Processes {

  def easilyConvertible(p: Process): Boolean = p match {
    case Affect(_,_) | Expr(_) | Send(_,_) => true
    case Block(stmts) => stmts forall easilyConvertible
    case _ => false
  }

}
