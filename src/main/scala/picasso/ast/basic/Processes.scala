package picasso.ast.basic

sealed abstract class Process
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
    var counter = 0
    def freshLoc: String = { //TODO Positional
      counter += 1
      id + "_loc_"+counter
    }
    def freshLocP(p: Process): PC = freshLoc
    def freshLocE(e: Expression): PC = freshLoc
    def mkCfa(init: PC, edge: Process, last: PC, assignTo: Option[String] = None): List[(PC, picasso.ast.Process, PC)] = edge match {
      case Affect(id /*String*/, value /*Expression*/) =>
        assert(assignTo.isEmpty)
        val id2 = picasso.ast.ID(picasso.math.hol.Variable(id)) //TODO type ?
        val value2 = Expressions.exp2Exp(value)
        List((init,picasso.ast.Affect(id2, value2),last))

      case Declaration(id /*String*/, mutable, value /*Expression*/) =>
        mkCfa(init, Affect(id, value), last, assignTo) //assume no name clash / shadowing

      case Expr(e /*Expression*/) =>
        List((init,picasso.ast.Expr(Expressions.exp2Exp(e)),last))

      case Send(dest /*Expression*/, content /*Expression*/) =>
        val dest2 = Expressions.exp2Exp(dest)
        val content2 = Expressions.exp2Exp(content)
        List((init,picasso.ast.Send(dest2, content2),last))

      case Receive(cases /*List[(Expression,Pattern,Process)]*/) => cases flatMap { case (expr, pat, p) =>
        val expr2 = Expressions.exp2Exp(expr)
        val pat2 = Patterns.pat2Pat(pat)
        val afterPattern = freshLocP(p)
        (init, picasso.ast.Receive(expr2, pat2), afterPattern) :: mkCfa(afterPattern, p, last, assignTo)
      }

      case Block(stmts) =>
        val newLocs = (stmts.tail) map freshLocP
        val inits = init :: newLocs
        val lasts = newLocs ::: List(last)
        assert(assignTo.isEmpty) //TODO assignTo ?
        stmts zip (inits zip lasts) flatMap {
          case (edge, (init, end)) => mkCfa(init, edge, end)
        }

      case ITE(condition, caseTrue, caseFalse) =>
        val cond = Expressions.exp2Exp(condition)
        val condFalse = picasso.ast.Application("!", List(cond))
        //true
        val trueCase = freshLocP(caseTrue)
        val trueGuard = picasso.ast.Assume(cond)
        ((init, trueGuard, trueCase)) :: mkCfa( trueCase, caseTrue, last, assignTo)
        //false
        val falseCase = freshLocP(caseFalse)
        val falseGuard = picasso.ast.Assume(condFalse)
        ((init, falseGuard, falseCase)) :: mkCfa( falseCase, caseFalse, last, assignTo)

      case While(condition, body) =>
        assert(assignTo.isEmpty)
        val cond = Expressions.exp2Exp(condition)
        val condFalse = picasso.ast.Application("!", List(cond))
        val loopBody = freshLocP(body)
        val trueGuard = picasso.ast.Assume(cond)
        val falseGuard = picasso.ast.Assume(condFalse)
        ((init, trueGuard, loopBody)) :: ((init,falseGuard,last)) :: mkCfa( loopBody, body, init)

      case ForEachGeneric(id /*String*/, set /*Expression*/, yieldOpt /*Option[(String,String)]*/, body) =>
        sys.error("TODO: ForEachGeneric")

    }
    val params2 = params map { id => picasso.ast.ID(picasso.math.hol.Variable(id)) } //TODO types ??
    val init = freshLoc
    val end = freshLoc
    val cfa = Automaton[GT.ELGT{type V = PC; type EL = picasso.ast.Process}](mkCfa(init, p, end), init, Set(end))
    new AgentDefinition[PC](id, params2, cfa)
  }

  /*
  case Affect(id: String, value: Expression)
  case Declaration(id: String, variable: Boolean, value: Expression)
  case Expr(e: Expression)
  case Send(dest: Expression, content: Expression)
  case Receive(cases: List[(Expression,Pattern,Process)])
  case Block(stmts: List[Process])
  //these things are expressible only at the agent level ...
  case ITE(condition: Expression, caseTrue: Process, caseFalse: Process)
  case While(condition: Expression, body: Process)
  case ForEachGeneric(id: String, set: Expression, yieldOpt: Option[(String,String)], body: Process)
  */

}

/* conversion to 
sealed abstract class Process {
case class Block(stmts: List[Process]) extends Process {
case class Affect(id: ID, value: Expression) extends Process {
case class Expr(e: Expression) extends Process {
case class Send(dest: Expression, content: Expression) extends Process {
case class Receive(src: Expression, pat: Pattern) extends Process {

object Skip { apply(), unapply(p: Process): Boolean
object Zero { apply(), unapply(p: Process): Boolean
//for collection use:
object EmptySet { apply(), unapply(e: Expression): Boolean
object SetIsEmpty { apply(e: Expression), unapply(e: Expression): Option[Expression]
object SetAdd { apply(e1: Expression, e2: Expression), unapply(e: Expression): Option[(Expression,Expression)]
object SetMinus { apply(e1: Expression, e2: Expression), unapply(e: Expression): Option[(Expression,Expression)]
object SetChoose { apply(e: Expression), unapply(e: Expression): Option[Expression]//do not remove the chosen element from the set
object SetPick { apply(e: Expression), unapply(e: Expression): Option[Expression]//do remove the chosen element from the set (this operation is not side-effect free)
*/
