package picasso.model.integer

import picasso.utils._

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

  def getPositiveNegativeTerms(e: Expression): (List[Expression], List[Expression]) = e match {
    case Plus(l,r) => 
      val (p1, n1) = getPositiveNegativeTerms(l)
      val (p2, n2) = getPositiveNegativeTerms(r)
      (p1 ::: p2, n1 ::: n2)
    case Minus(l,r) => 
      val (p1, n1) = getPositiveNegativeTerms(l)
      val (p2, n2) = getPositiveNegativeTerms(r)
      (p1 ::: n2, n1 ::: p2)
    case UMinus(u) => 
      val (p, n) = getPositiveNegativeTerms(u)
      (n, p)
    case cstOrVar => (List(cstOrVar), Nil)
  }
  
  def getPositiveTerms(e: Expression) = getPositiveNegativeTerms(e)._1

  def getNegativeTerms(e: Expression) = getPositiveNegativeTerms(e)._2

  /** Returns a list of variables with positive polarity, then negative variables, then constant */
  def decompose(e: Expression): (List[Variable], List[Variable], Constant) = {
    val (pos, neg) = getPositiveNegativeTerms(e)
    val (posVar, posCst) = pos.partition{
        case Variable(_) => true
        case Constant(_) => false
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable or Constant, found: " + other)
      }
    val (negVar, negCst) = neg.partition{
        case Variable(_) => true
        case Constant(_) => false
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable or Constant, found: " + other)
      }
    val posVar2: List[Variable] = posVar.map{
        case v @ Variable(_) => v
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable, found: " + other)
      }
    val negVar2: List[Variable] = negVar.map{
        case v @ Variable(_) => v
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable, found: " + other)
      }
    val cst1 = (0 /: posCst)( (acc, c) => c match {
        case Constant(value) => acc + value
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Constant, found: " + other)
      })
    val cst2 = (cst1 /: negCst)( (acc, c) => c match {
        case Constant(value) => acc - value
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Constant, found: " + other)
      })
    //var that are added and removed -> sum to 0
    val posMS = MultiSet(posVar2:_*)
    val negMS = MultiSet(negVar2:_*)
    val posVar3 = posMS -- negMS
    val negVar3 = negMS -- posMS
    (posVar3.toList, negVar3.toList, Constant(cst2))
  }

  def recompose(pos: List[Variable], neg: List[Variable], cst: Constant): Expression = {
    val posSum = if (pos.isEmpty) None else Some((pos: List[Expression]).reduceLeft(Plus(_, _)))
    val afterSubtract =
      if (posSum.isDefined) Some( (posSum.get /: neg)( (acc, v) => Minus(acc, v) ) )
      else if (neg.isEmpty) None
      else Some( UMinus((neg: List[Expression]).reduceLeft(Plus(_,_))) )
    if (afterSubtract.isEmpty) cst
    else if (cst.i == 0) afterSubtract.get
    else if (cst.i > 0) Plus(afterSubtract.get, cst)
    else Minus(afterSubtract.get, Constant(- cst.i))
  }

  def simplify(e: Expression): Expression = {
    val (p, n, c) = decompose(e)
    recompose(p,n,c)
  }

  //TODO lazyCopier
  def alpha(e: Expression, subst: Map[Variable,Expression]): Expression = e match {
    case Plus(l,r) => Plus(alpha(l, subst), alpha(r, subst)) 
    case Minus(l,r) => Minus(alpha(l, subst), alpha(r, subst)) 
    case UMinus(u) => UMinus(alpha(u, subst)) 
    case c @ Constant(_) => c
    case v @ Variable(_) => subst.getOrElse(v, v)
  }

}

//TODO the new vs old variable convention needs to be made cleaner ...
abstract class Statement 
case class Transient(v: Variable) extends Statement //declare a local variable (used only in the initialization)
case class Relation(_new: Expression, _old: Expression) extends Statement //eqality between an expr on new variables and an expr on old variables
case class Variance(_new: Variable, _old: Variable, greater: Boolean = true, strict: Boolean = false) extends Statement //When a variable change and we need to force a 'direction' (used in the unfolding)
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
    case Variance(n, o, _, _) => Set(n, o)
    case _ => Set()
  }

  def getTransientVariables(s: Statement): Set[Variable] = s match {
    case Transient(v) => Set(v)
    case _ => Set()
  }

  def getUpdatedVars(s: Statement): Set[Variable] = s match {
    case Relation(n, _) => Expression.variables(n)
    case Assume(c) => Condition.variables(c)
    case Variance(v, _, _, _) => Set(v)
    case _ => Set()
  }

  def print(s: Statement): String = s match {
    case Transient(v) => "transient("+v.name+")"
    case Relation(_new, _old) => Expression.print(_new) + "=" + Expression.print(_old)
    case Skip => "skip"
    case Assume(c) => "assume("+Condition.print(c)+")"
    case Variance(v1, v2, geq, strict) => v1.name + (if (geq) " is greater " else " is smaller ") + (if (strict) "(strictly) " else "") + "than " + v2.name
  }

  def alpha(s: Statement, subst: Map[Variable, Expression]): Statement = s match {
    case Relation(n, o) => Relation(Expression.alpha(n, subst), Expression.alpha(o, subst))
    case Assume(c) => Assume(Condition.alpha(c, subst))
    case tr @ Transient(t) => assert(!subst.contains(t)); tr
    case vr @ Variance(v1, v2, geq, strict) =>
      if (subst.contains(v1)) {
        subst(v1) match {
          case v3 @ Variable(_) =>
            subst.get(v2) match {
              case Some(v4 @ Variable(_)) => Variance(v3, v4, geq, strict)
              case Some(c @ Constant(_)) =>
                val (small, big) = if (geq) (c, v3) else (v3, c)
                val cond = if (strict) Lt(small, big) else Leq(small, big)
                Assume(cond)
              case Some(other) => Logger.logAndThrow("integer.AST", LogError, "alpha of Variance (new), expected Variable or Constant, found: " + other)
              case None => Variance(v3, v2, geq, strict)
            }
          case other => Logger.logAndThrow("integer.AST", LogError, "alpha of Variance (new), expected Variable, found: " + other)
        }
      } else if (subst.contains(v2)) {
        subst(v2) match {
          case v3 @ Variable(_) => Variance(v1, v3, geq, strict)
          case c @ Constant(_) =>
            val (small, big) = if (geq) (c, v1) else (v1, c)
            val cond = if (strict) Lt(small, big) else Leq(small, big)
            Assume(cond)
          case other => Logger.logAndThrow("integer.AST", LogError, "alpha of Variance (old), expected Variable or Constant, found: " + other)
        }
      } else {
        vr
      }
    case Skip => Skip
  }

  def alphaPre(s: Statement, subst: Map[Variable, Expression]): Statement = s match {
    case Relation(n, o) => Relation(n, Expression.alpha(o, subst))
    case tr @ Transient(t) => assert(!subst.contains(t)); tr
    case vr @ Variance(v3, v, geq, strict) =>
      if (subst.contains(v)) {
        subst(v) match {
          case v2 @ Variable(_) => Variance(v2, v3, geq, strict)
          case c @ Constant(_) =>
            if (geq && strict) Assume(Lt(c, v))
            else if (geq && !strict) Assume(Leq(c, v))
            else if (!geq && strict) Assume(Lt(v, c))
            else Assume(Leq(v, c))
          case other => Logger.logAndThrow("integer.AST", LogError, "alphaPre of Variance, expected Variable or Constant, found: " + other)
        }
      } else {
        vr
      }
    case other => other
  }

  def alphaPost(s: Statement, subst: Map[Variable, Expression]): Statement = s match {
    case Relation(n, o) => Relation(Expression.alpha(n, subst), o)
    case Assume(c) => Assume(Condition.alpha(c, subst))
    case tr @ Transient(t) => assert(!subst.contains(t)); tr
    case vr @ Variance(v, v2, geq, strict) =>
      if (subst.contains(v2)) {
        subst(v2) match {
          case v3 @ Variable(_) => Variance(v, v3, geq, strict)
          case other => Logger.logAndThrow("integer.AST", LogError, "alphaPost of Variance, expected Variable, found: " + other)
        }
      } else vr
    case other => other
  }

  //some very simple simplifications to make the printing easier
  def simplify(s: Statement): Statement = s match {
    case Relation(e1, e2) =>
      val se1 = Expression.simplify(e1)
      val se2 = Expression.simplify(e2)
      (se1, se2) match {
        case (Constant(c1), Constant(c2)) => assert(c1 == c2); Skip
        case _ => Relation(se1, se2)
      }
    case Assume(c) =>
      Condition.simplify(c) match {
        case Literal(true) => Skip
        case c2 => Assume(c2)
      }
    case other => other
  }

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

  def simplify(c: Condition): Condition = c match {
    case l @ Literal(_) => l
    case e @ Eq(Constant(c1), Constant(c2)) => if (c1 == c2) Literal(true) else Literal(false)
    case e @ Eq(e1, e2) => if (e1 == e2) Literal(true) else e
    case e @ Leq(Constant(c1), Constant(c2)) => if (c1 <= c2) Literal(true) else Literal(false)
    case e @ Leq(e1, e2) => if (e1 == e2) Literal(true) else e
    case e @ Lt(Constant(c1), Constant(c2)) => if (c1 < c2) Literal(true) else Literal(false)
    case e @ Lt(e1, e2) => if (e1 == e2) Literal(false) else e
    case And(c1, c2) =>
      val c1s = simplify(c1)
      val c2s = simplify(c2)
      (c1s, c2s) match {
        case (Literal(true), c2s) => c2s
        case (c1s, Literal(true)) => c1s
        case (Literal(false), _) => Literal(false)
        case (_, Literal(false)) => Literal(false)
        case (c1s, c2s) => if (c1s == c2s) c1s else And(c1s, c2s)
      }
    case Or(c1, c2) =>
      val c1s = simplify(c1)
      val c2s = simplify(c2)
      (c1s, c2s) match {
        case (Literal(false), c2s) => c2s
        case (c1s, Literal(false)) => c1s
        case (Literal(true), _) => Literal(true)
        case (_, Literal(true)) => Literal(true)
        case (c1s, c2s) => if (c1s == c2s) c1s else Or(c1s, c2s)
      }
    case Not(c1) =>
      nnf(Not(simplify(c1)))
  }
  
  //TODO lazyCopier
  def alpha(c: Condition, subst: Map[Variable,Expression]): Condition = c match {
    case Eq(l,r) => Eq(Expression.alpha(l, subst), Expression.alpha(r, subst))
    case Lt(l,r) => Lt(Expression.alpha(l, subst), Expression.alpha(r, subst))
    case Leq(l,r) => Leq(Expression.alpha(l, subst), Expression.alpha(r, subst))
    case And(l,r) => And(alpha(l, subst), alpha(r, subst))
    case Or(l,r) => Or(alpha(l, subst), alpha(r, subst))
    case Not(c) => Not(alpha(c, subst))
    case l @ Literal(_) => l
  }

}
