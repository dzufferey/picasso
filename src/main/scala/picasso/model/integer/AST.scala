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

}

abstract class Statement 
case class Affect(v: Variable, rhs: Expression) extends Statement
case class Havoc(v: Variable) extends Statement

abstract class Condition
case class Eq(l: Expression, r: Expression) extends Condition
case class Lt(l: Expression, r: Expression) extends Condition
case class Leq(l: Expression, r: Expression) extends Condition
case class And(l: Condition, r: Condition) extends Condition
case class Or(l: Condition, r: Condition) extends Condition
case class Not(c: Condition) extends Condition

object Condition {

  def priority(e: Condition): Int = e match {
    case Eq(_,_) => 30
    case Lt(_,_) => 30
    case Leq(_,_) => 30
    case And(_,_) => 11
    case Or(_,_) => 10
    case Not(_) => 20
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
  }

}
