package picasso.model.integer

abstract class Expression 
case class Plus(l: Expression, r: Expression) extends Expression 
case class Minus(l: Expression, r: Expression) extends Expression 
case class UMinus(e: Expression) extends Expression 
case class Constant(i: Int) extends Expression 
case class Variable(name: String) extends Expression 

object Expression {

  def priority(e: Expression): Int = e match {
    case Plus(_,_) => 11
    case Minus(_,_) => 10
    case UMinus(_) => 20
    case Constant(_) => 30
    case Variable(_) => 30
  }

  def needParenthesis(currentPriority: Int, e: Expression): String = {
    if (priority(e) < currentPriority) "(" + print(e) + ")"
    else print(e)
  }

  def print(e: Expression): String = e match {
    case Plus(l,r) => needParenthesis(priority(e), l) + " + " + needParenthesis(priority(e), r)
    case Minus(l,r) => needParenthesis(priority(e), l) + " - " + needParenthesis(priority(e), r)
    case UMinus(u) => "-" + needParenthesis(priority(e), u)
    case Constant(c) => c.toString
    case Variable(v) => v
  }

  def variables(e: Expression): Set[Variable] = e match {
    case Plus(l,r) => variables(l) ++ variables(r)
    case Minus(l,r) => variables(l) ++ variables(r)
    case UMinus(u) => variables(u)
    case Constant(_) => Set()
    case v @ Variable(_) => Set(v)
  }

}

//TODO the new vs old variable convention needs to be made cleaner ...
abstract class Statement 
case class Transient(v: Variable) extends Statement //declare a local variable
case class Relation(_new: Expression, _old: Expression) extends Statement //eqality between an expr on new variables and an expr on old variables
case object Skip extends Statement
case class Assume(c: Condition) extends Statement //one the transient and new variables

object Affect {
  def apply(v: Variable, rhs: Expression) = Relation(v, rhs)
  def unapply(rel: Relation): Option[(Variable, Expression)] = rel match {
    case Relation(v @ Variable(_), rhs) => Some(v -> rhs)
    case _ => None
  }
}

object Statement {

  def getAllVariables(s: Statement): Set[Variable] = s match {
    case Relation(n, o) => Expression.variables(n) ++ Expression.variables(o)
    case Assume(c) => Condition.variables(c)
    case _ => Set()
  }

  def getTransientVariables(s: Statement): Set[Variable] = s match {
    case Transient(v) => Set(v)
    case _ => Set()
  }

  def getUpdatedVars(s: Statement): Set[Variable] = s match {
    case Relation(n, _) => Expression.variables(n)
    case Assume(c) => Condition.variables(c)
    case _ => Set()
  }

  /*
  def variables(s: Statement): Set[Variable] = {
    getAllVariables(s) -- getTransientVariables(s)
  }
  */
}

abstract class Condition
case class Eq(l: Expression, r: Expression) extends Condition
case class Lt(l: Expression, r: Expression) extends Condition
case class Leq(l: Expression, r: Expression) extends Condition
case class And(l: Condition, r: Condition) extends Condition
case class Or(l: Condition, r: Condition) extends Condition
case class Not(c: Condition) extends Condition
case class Literal(b: Boolean) extends Condition

object Condition {

  def priority(e: Condition): Int = e match {
    case Eq(_,_) => 30
    case Lt(_,_) => 30
    case Leq(_,_) => 30
    case And(_,_) => 11
    case Or(_,_) => 10
    case Not(_) => 20
    case Literal(_) => 30
  }
  
  def needParenthesis(currentPriority: Int, e: Condition): String = {
    if (priority(e) < currentPriority) "(" + print(e) + ")"
    else print(e)
  }
  
  def print(e: Condition): String = e match {
    case Eq(l,r) =>  l + " == " + r
    case Lt(l,r) =>   l + " < " + r
    case Leq(l,r) =>  l + " <= " + r
    case And(l,r) =>  needParenthesis(priority(e), l) + " && " + needParenthesis(priority(e), r)
    case Or(l,r) =>  needParenthesis(priority(e), l) + " || " + needParenthesis(priority(e), r)
    case Not(c) =>  "!" + needParenthesis(priority(e), c) 
    case Literal(b) => b.toString
  }

  def variables(c: Condition): Set[Variable] = c match {
    case Eq(l,r) => Expression.variables(l) ++ Expression.variables(r)
    case Lt(l,r) => Expression.variables(l) ++ Expression.variables(r)
    case Leq(l,r) => Expression.variables(l) ++ Expression.variables(r)
    case And(l,r) => variables(l) ++ variables(r)
    case Or(l,r) => variables(l) ++ variables(r)
    case Not(c) => variables(c)
    case Literal(_) => Set()
  }

  def nnf(c: Condition): Condition = {
    def process(c: Condition, negate: Boolean): Condition = c match {
      case e @ Eq(_,_) => if (negate) Not(e) else e
      case Lt(l,r) => if (negate) Leq(r,l) else Lt(l,r)
      case Leq(l,r) => if (negate) Lt(r,l) else Leq(l,r)
      case And(l,r) =>
        val l2 = process(l, negate)
        val r2 = process(r, negate)
        if (negate) Or(l2, r2) else And(l2, r2)
      case Or(l,r) => 
        val l2 = process(l, negate)
        val r2 = process(r, negate)
        if (negate) And(l2, r2) else Or(l2, r2)
      case Not(c) => process(c, !negate)
      case Literal(b) => if (negate) Literal(!b) else Literal(b)
    }
    process(c, false)
  }

}
