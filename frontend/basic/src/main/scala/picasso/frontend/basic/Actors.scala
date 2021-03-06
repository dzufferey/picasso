package picasso.frontend.basic

import picasso.ast.AgentDefinition
import picasso.graph._
import picasso.utils.Misc
import picasso.transform.BooleanFunctions

case class Actor(id: String, params: List[ID], body: Process) extends scala.util.parsing.input.Positional with Sym with Typed {
  override def toString = {
    id + params.map(_.toStringFull).mkString("(",", ",")") + "\n" + Misc.indent("  ", body.toString)
  }
}

object Actors {
  
  type PC = String

  def actor2Agent(a: Actor): AgentDefinition[PC] = {
    val id = a.id
    val params = a.params
    def freshLoc(where: scala.util.parsing.input.Positional): String = id+"("+where.pos+")"
    def mkCfa(init: PC, edge: Process, last: PC): List[(PC, picasso.ast.Process, PC)] = edge match {
      case Affect(id /*ID*/, value /*Expression*/) =>
        val id2 = Expressions.id2ID(id)
        val value2 = Expressions.exp2ExpSimplify(value)
        List((init,picasso.ast.Affect(id2, value2),last))

      case Declaration(id /*ID*/, mutable, value /*Expression*/) =>
        mkCfa(init, Affect(id, value), last) //assume no name clash / shadowing

      case Expr(e /*Expression*/) =>
        List((init,picasso.ast.Expr(Expressions.exp2ExpSimplify(e)),last))

      case Send(dest /*Expression*/, content /*Expression*/) =>
        val dest2 = Expressions.exp2ExpSimplify(dest)
        val content2 = Expressions.exp2ExpSimplify(content)
        List((init,picasso.ast.Send(dest2, content2),last))

      case Receive(cases /*List[(Expression,Pattern,Process)]*/) => cases flatMap { case (expr, pat, p) =>
        val expr2 = Expressions.exp2ExpSimplify(expr)
        val pat2 = Patterns.pat2Pat(pat)
        val afterPattern = freshLoc(p)
        (init, picasso.ast.Receive(expr2, pat2), afterPattern) :: mkCfa(afterPattern, p, last)
      }
      
      case Zero() =>
        List((init,picasso.ast.Zero(),last))

      case Block(stmts) =>
        //TODO Block(Nil) is Zero
        val newLocs = (stmts.tail) map freshLoc
        val inits = init :: newLocs
        val lasts = newLocs ::: List(last)
        stmts zip (inits zip lasts) flatMap {
          case (edge, (init, end)) => mkCfa(init, edge, end)
        }

      case ITE(condition, caseTrue, caseFalse) =>
        val cond = Expressions.exp2ExpSimplify(condition)
        val condFalse = BooleanFunctions.groundTermSimplification(picasso.ast.Application("!", List(cond)))
        //true
        val trueCase = freshLoc(caseTrue)
        val trueGuard = picasso.ast.Assume(cond)
        val trueEdges = ((init, trueGuard, trueCase)) :: mkCfa( trueCase, caseTrue, last)
        //false
        val falseCase = freshLoc(caseFalse)
        val falseGuard = picasso.ast.Assume(condFalse)
        val falseEdges = ((init, falseGuard, falseCase)) :: mkCfa( falseCase, caseFalse, last)
        trueEdges ::: falseEdges

      case While(condition, body) =>
        val cond = Expressions.exp2ExpSimplify(condition)
        val condFalse = BooleanFunctions.groundTermSimplification(picasso.ast.Application("!", List(cond)))
        val loopBody = freshLoc(body)
        val trueGuard = picasso.ast.Assume(cond)
        val falseGuard = picasso.ast.Assume(condFalse)
        ((init, trueGuard, loopBody)) :: ((init,falseGuard,last)) :: mkCfa( loopBody, body, init)

      case ForEachGeneric(id, set , yieldOpt /*Option[(ID,ID)]*/, body) =>
        assert(yieldOpt.isEmpty, "\"for yield\" is not yet supported.")
        val iterator = Expressions.id2ID(ID("_PICASSO_iterator") setType set.tpe)
        val pre = freshLoc(set)
        val warmup = (init, picasso.ast.Affect(iterator, picasso.ast.SetCopy(Expressions.exp2ExpSimplify(set))), pre)
        val looping = freshLoc(body)
        val enteringLoop = (pre, picasso.ast.Affect(Expressions.id2ID(id), picasso.ast.SetPick(iterator)), looping)
        val exitingLoop = (pre, picasso.ast.Assume(picasso.ast.SetIsEmpty(iterator)), last)
        warmup :: enteringLoop :: exitingLoop :: mkCfa(looping, body, pre)

    }
    val params2 = params map Expressions.id2ID
    val init = id + "_start" 
    val end = id + "_end"
    val edges = mkCfa(init, a.body, end)
    val cfa = Automaton[GT.ELGT{type V = PC; type EL = picasso.ast.Process}](edges, init, Set(end))
    //TODO the whole thing might need types
    (new AgentDefinition[PC](id, params2, cfa)).compact
  }

}
