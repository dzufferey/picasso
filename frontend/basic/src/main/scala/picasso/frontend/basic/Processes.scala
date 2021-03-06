package picasso.frontend.basic

import picasso.utils.Misc

sealed abstract class Process extends scala.util.parsing.input.Positional 
case class Block(stmts: List[Process]) extends Process {
  override def toString = "begin\n" + Misc.indent("  ", stmts.mkString("",";\n","")) + "\nend\n"
}
case class Affect(id: ID, value: Expression) extends Process {
  override def toString = id + " := " + value
}
case class Declaration(id: ID, variable: Boolean, value: Expression) extends Process {
  override def toString = (if (variable) "var " else "val ") + id.toStringFull + " := " + value
}
case class Expr(e: Expression) extends Process {
  override def toString = e.toString
}
case class Send(dest: Expression, content: Expression) extends Process {
  override def toString = dest + " ! " + content
}
case class Receive(cases: List[(Expression,Pattern,Process)]) extends Process {
  override def toString = {
    val cases1 = cases.map{ case (e,pa,po) =>
      e + " ? " + pa.toStringFull + " =>\n" + Misc.indent("  ", po.toString)
    }
    val casesStr = cases1.map(Misc.indent("  ",_)).mkString("","\n","")
    "select\n" + casesStr
  }
}
case class ITE(condition: Expression, caseTrue: Process, caseFalse: Process) extends Process {
  override def toString = "if "+condition+" then\n" + Misc.indent("  ", caseTrue.toString) + "\nelse\n" + Misc.indent("  ", caseFalse.toString)
}
case class While(condition: Expression, body: Process) extends Process {
  override def toString = "while "+condition+" do\n"+ Misc.indent("  ", body.toString)
}
//foreach VAR in COLLECTION do BODY
//foreach VAR1 in COLLECTION1 do BODY yield VAR2 in COLLECTION2
case class ForEachGeneric(id: ID, set: Expression, yieldOpt: Option[(ID,ID)], body: Process) extends Process {
}

object Skip {
  def apply() = Expr(Unit())
  def unapply(p: Expr): Boolean = p match {
    case Expr(Unit()) => true
    case _ => false
  }
}

object Zero {
  def apply() = Block(Nil)
  def unapply(p: Process): Boolean = p match {
    case Block(Nil) | Receive(Nil) | Block(Receive(Nil) :: Nil) => true
    case _ => false
  }
}

object ForEach {
  def apply(id: ID, set: Expression, body: Process) = ForEachGeneric(id, set, None, body)
  def unapply(p: ForEachGeneric): Option[(ID, Expression, Process)] = p match {
    case ForEachGeneric(id, set, None, body) => Some((id, set, body))
    case _ => None
  }
}

object ForEachYield {
  def apply(x: ID, setX: Expression, y: ID, setY: ID,  body: Process) = ForEachGeneric(x, setX, Some((y, setY)), body)
  def unapply(p: ForEachGeneric): Option[(ID, Expression, ID, ID, Process)] = p match {
    case ForEachGeneric(id, setId, Some((y,sy)), body) => Some((id, setId, y, sy, body))
    case _ => None
  }
}

