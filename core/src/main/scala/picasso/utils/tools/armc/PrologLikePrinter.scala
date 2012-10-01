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

  protected def primeNotTransient(e: Expression, transient: Set[Variable]): Expression = e match {
    case Plus(l,r) => Plus(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Minus(l,r) => Minus(primeNotTransient(l, transient), primeNotTransient(r, transient))
    //case UMinus(u) => UMinus(primeNotTransient(u, transient))
    case c @ Constant(_) => c
    case v @ Variable(_) => if (transient(v)) v else primeVar(v)
  }

  protected def primeNotTransient(c: Condition, transient: Set[Variable]): Condition = c match {
    case Eq(l,r) => Eq(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Lt(l,r) => Lt(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Leq(l,r) => Leq(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case And(l,r) => And(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Or(l,r) => Or(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Not(c) => Not(primeNotTransient(c, transient))
    case l @ Literal(_) => l
  }

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
    case And(l,r) => printCondition(l) + ", " + printCondition(r) 
    case err @ Or(l,r) => Logger.logAndThrow("PrologLikePrinter", LogError, "Or not yet supported:  " + err)
    case err @ Not(c) =>  Logger.logAndThrow("PrologLikePrinter", LogError, "Not not yet supported:  " + err)
    case Literal(b) => if (b) "0 = 0" else "1 = 0"
  }

  protected def makeConditionNice(c: Condition): Seq[Condition] = {
    //flatten the And, remove the literals, ... 
    def flatten(c: Condition, acc: List[Condition]): List[Condition] = c match {
      case And(l,r) => flatten(r, flatten(l, acc))
      case err @ Or(l,r) => Logger.logAndThrow("PrologLikePrinter", LogError, "Or not yet supported:  " + err)
      case err @ Not(c) =>  Logger.logAndThrow("PrologLikePrinter", LogError, "Not not yet supported:  " + err)
      case Literal(b) => if (b) acc else List(Literal(false))
      case other => other :: acc
    }
    flatten(Condition.nnf(c), Nil)
  }

  protected def transitionConstraints(t: Transition, frame: Seq[Statement] = Seq()): Seq[Condition] = {
    val transient = t.transientVariables
    makeConditionNice(t.guard) ++ ((t.updates ++ frame) flatMap {
      case Skip | Transient(_) => Seq()
      case Relation(n, o) => makeConditionNice(Eq(primeNotTransient(n, transient), o))
      case Assume(c) => makeConditionNice(primeNotTransient(c, transient))
      case Variance(v, v2, geq, strict) =>
        val v3 = primeNotTransient(v, transient)
        if (geq && strict) Seq(Lt(v2, v3))
        else if (geq && !strict) Seq(Leq(v2, v3))
        else if (!geq && strict) Seq(Lt(v3, v2))
        else Seq(Leq(v3, v2))
    })
  }

}
