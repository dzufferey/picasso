package picasso.utils.tools.armc

import picasso.model.integer._
import java.io._
import scala.collection.GenSeq
import picasso.utils._
import picasso.graph._

class PrologLikePrinter {

  protected def asLit(str: String): String = {
    assert(str.length > 0)
    if (str(0).isLower) str.replace("$","_")
    else str.updated(0, str(0).toLower).replace("$","_")
  }
  
  protected def asVar(str: String): String = {
    assert(str.length > 0)
    if (str(0).isUpper) str.replace("$","_")
    else str.updated(0, str(0).toUpper).replace("$","_")
  }
  protected def asVar(v: Variable): String = asVar(v.name)

  protected def primeVar(v: Variable): Variable = Variable(v.name + "_prime")

  protected def needParenthesis(currentPriority: Int, e: Expression): String = {
    if (Expression.priority(e) < currentPriority) "(" + printExpression(e) + ")"
    else printExpression(e)
  }
  protected def printExpression(e: Expression): String = e match {
    case Plus(l,r) => needParenthesis(Expression.priority(e), l) + " + " + needParenthesis(Expression.priority(e), r)
    case Minus(l,r) => needParenthesis(Expression.priority(e), l) + " - " + needParenthesis(Expression.priority(e), r)
    //case UMinus(u) => "-" + needParenthesis(Expression.priority(e), u)
    case Constant(c) => c.toString
    case Variable(v) => asVar(v)
  }

  protected def printCondition(c: Condition): String = c match {
    case Eq(l,r) =>  printExpression(l) + " = " + printExpression(r)
    case Lt(l,r) =>  printExpression(l) + " < " + printExpression(r)
    case Leq(l,r) => printExpression(l) + " =< " + printExpression(r)
    case And(lst) => lst.map(printCondition).mkString(", ")
    case err @ Or(_) => Logger.logAndThrow("PrologLikePrinter", LogError, "Or not yet supported:  " + err)
    case err @ Not(c) =>  Logger.logAndThrow("PrologLikePrinter", LogError, "Not not yet supported:  " + err)
    case Literal(b) => if (b) "0 = 0" else "1 = 0"
  }

}
