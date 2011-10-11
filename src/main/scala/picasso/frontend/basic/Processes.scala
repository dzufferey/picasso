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

  import picasso.ast.AgentDefinition
  import picasso.graph._

  def easilyConvertible(p: Process): Boolean = p match {
    case Affect(_,_) | Expr(_) | Send(_,_) => true
    case Block(stmts) => stmts forall easilyConvertible
    case _ => false
  }

  //TODO make everything scala.util.parsing.input.Positional
  type PC = String

  //if not easilyConvertible then translate to AgentDefinition
  def toAgent(id: String, params: List[String], p: Process): AgentDefinition[PC] = {
    def freshLoc(where: scala.util.parsing.input.Positional): String = id+"("+where.pos+")"
    def mkCfa(init: PC, edge: Process, last: PC): List[(PC, picasso.ast.Process, PC)] = edge match {
      case Affect(id /*String*/, value /*Expression*/) =>
        val id2 = picasso.ast.ID(picasso.math.hol.Variable(id)) //TODO type ?
        val value2 = Expressions.exp2Exp(value)
        List((init,picasso.ast.Affect(id2, value2),last))

      case Declaration(id /*String*/, mutable, value /*Expression*/) =>
        mkCfa(init, Affect(id, value), last) //assume no name clash / shadowing

      case Expr(e /*Expression*/) =>
        List((init,picasso.ast.Expr(Expressions.exp2Exp(e)),last))

      case Send(dest /*Expression*/, content /*Expression*/) =>
        val dest2 = Expressions.exp2Exp(dest)
        val content2 = Expressions.exp2Exp(content)
        List((init,picasso.ast.Send(dest2, content2),last))

      case Receive(cases /*List[(Expression,Pattern,Process)]*/) => cases flatMap { case (expr, pat, p) =>
        val expr2 = Expressions.exp2Exp(expr)
        val pat2 = Patterns.pat2Pat(pat)
        val afterPattern = freshLoc(p)
        (init, picasso.ast.Receive(expr2, pat2), afterPattern) :: mkCfa(afterPattern, p, last)
      }

      case Block(stmts) =>
        //TODO Block(Nil) is Zero
        val newLocs = (stmts.tail) map freshLoc
        val inits = init :: newLocs
        val lasts = newLocs ::: List(last)
        stmts zip (inits zip lasts) flatMap {
          case (edge, (init, end)) => mkCfa(init, edge, end)
        }

      case ITE(condition, caseTrue, caseFalse) =>
        val cond = Expressions.exp2Exp(condition)
        val condFalse = picasso.ast.Application("!", List(cond))
        //true
        val trueCase = freshLoc(caseTrue)
        val trueGuard = picasso.ast.Assume(cond)
        ((init, trueGuard, trueCase)) :: mkCfa( trueCase, caseTrue, last)
        //false
        val falseCase = freshLoc(caseFalse)
        val falseGuard = picasso.ast.Assume(condFalse)
        ((init, falseGuard, falseCase)) :: mkCfa( falseCase, caseFalse, last)

      case While(condition, body) =>
        val cond = Expressions.exp2Exp(condition)
        val condFalse = picasso.ast.Application("!", List(cond))
        val loopBody = freshLoc(body)
        val trueGuard = picasso.ast.Assume(cond)
        val falseGuard = picasso.ast.Assume(condFalse)
        ((init, trueGuard, loopBody)) :: ((init,falseGuard,last)) :: mkCfa( loopBody, body, init)

      case ForEachGeneric(id /*String*/, set /*Expression*/, yieldOpt /*Option[(String,String)]*/, body) =>
        sys.error("TODO: ForEachGeneric")

    }
    val params2 = params map { id => picasso.ast.ID(picasso.math.hol.Variable(id)) } //TODO types ??
    val init = id + "_start" 
    val end = id + "_end"
    val cfa = Automaton[GT.ELGT{type V = PC; type EL = picasso.ast.Process}](mkCfa(init, p, end), init, Set(end))
    //TODO the whole thing might need types
    new AgentDefinition[PC](id, params2, cfa)
  }

}
