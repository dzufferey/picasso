package picasso.model.integer

import picasso.utils._

sealed abstract class Expression 
case class Plus(l: Expression, r: Expression) extends Expression 
case class Minus(l: Expression, r: Expression) extends Expression 
case class Constant(i: Int) extends Expression {
  override def toString = i.toString
}
case class Variable(name: String) extends Expression {
  override def toString = name
}

object Expression {

  def priority(e: Expression): Int = e match {
    case Plus(_,_) => 10
    case Minus(_,_) => 15
    case Constant(_) | Variable(_) => 20
  }

  def needParenthesis(currentPriority: Int, e: Expression): String = {
    if (priority(e) < currentPriority) "(" + print(e) + ")"
    else print(e)
  }

  def print(e: Expression): String = e match {
    case Plus(l,r) => needParenthesis(priority(e), l) + " + " + needParenthesis(priority(e), r)
    case Minus(l,r) => needParenthesis(priority(e), l) + " + " + needParenthesis(priority(e), r)
    case Constant(c) => c.toString
    case Variable(v) => v
  }

  def variables(e: Expression): Set[Variable] = e match {
    case Plus(l,r) => variables(l) ++ variables(r)
    case Minus(l,r) => variables(l) ++ variables(r)
    case Constant(_) => Set()
    case v @ Variable(_) => Set(v)
  }

  def getTerms(e: Expression): List[Expression] = e match {
    case Plus(l,r) => getTerms(l) ::: getTerms(r)
    //case Minus(l,r) => getTerms(l) ::: getTerms(r)
    case cstOrVar => List(cstOrVar)
  }
  
  def getPosTerms(e: Expression): List[Expression] = e match {
    case Plus(l,r) => getPosTerms(l) ::: getPosTerms(r)
    case Minus(l,r) => getPosTerms(l) ::: getNegTerms(r)
    case cstOrVar => List(cstOrVar)
  }
  
  def getNegTerms(e: Expression): List[Expression] = e match {
    case Plus(l,r) => getNegTerms(l) ::: getNegTerms(r)
    case Minus(l,r) => getNegTerms(l) ::: getPosTerms(r)
    case cstOrVar => List(cstOrVar)
  }
  
  def getPosNegTerms(e: Expression): (List[Expression], List[Expression]) = e match {
    case Plus(l,r) =>
      val (p1, n1) = getPosNegTerms(l)
      val (p2, n2) = getPosNegTerms(r)
      (p1 ::: p2, n1 ::: n2)
    case Minus(l,r) =>
      val (p1, n1) = getPosNegTerms(l)
      val (p2, n2) = getPosNegTerms(r)
      (p1 ::: n2, n1 ::: p2)
    case cstOrVar => (List(cstOrVar), Nil)
  }
  
  def decomposePosNeg(e: Expression): (List[Variable], List[Variable], Constant) = {
    val (pos, neg) = getPosNegTerms(e)
    val (pVars, pCst) = ( (List[Variable](), 0) /: pos)( (acc, p) => p match {
      case v @ Variable(_) => (v :: acc._1, acc._2)
      case Constant(c) => (acc._1, acc._2 + c)
      case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable or Constant, found: " + other)
    })
    val (nVars, nCst) = ( (List[Variable](), 0) /: neg)( (acc, p) => p match {
      case v @ Variable(_) => (v :: acc._1, acc._2)
      case Constant(c) => (acc._1, acc._2 + c)
      case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable or Constant, found: " + other)
    })
    (pVars, nVars, Constant(pCst - nCst))
  }

  /** Returns a list of variables with positive polarity, then negative variables, then constant */
  def decompose(e: Expression): (List[Variable], Constant) = {
    val pos = getTerms(e)
    val (posVar, posCst) = pos.partition{
        case Variable(_) => true
        case Constant(_) => false
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable or Constant, found: " + other)
      }
    val posVar2: List[Variable] = posVar.map{
        case v @ Variable(_) => v
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable, found: " + other)
      }
    val cst = (0 /: posCst)( (acc, c) => c match {
        case Constant(value) => acc + value
        case other => Logger.logAndThrow("integer.AST", LogError, "expected Constant, found: " + other)
      })
    (posVar2, Constant(cst))
  }

  //returns a vector of coefficients (variables) and a constant term.
  def decomposeVector(e: Expression, idxMap: Map[Variable, Int]): (Array[Int], Int) = {
    val coeffArray = Array.ofDim[Int](idxMap.size)
    var constantTerm = 0
    val (pos, neg) = getPosNegTerms(e)
    pos.foreach{
      case v @ Variable(_) => coeffArray(idxMap(v)) += 1
      case Constant(c) => constantTerm += c
      case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable or Constant, found: " + other)
    }
    neg.foreach{
      case v @ Variable(_) => coeffArray(idxMap(v)) -= 1
      case Constant(c) => constantTerm -= c
      case other => Logger.logAndThrow("integer.AST", LogError, "expected Variable or Constant, found: " + other)
    }
    (coeffArray, constantTerm)
  }
  def decomposeVector(e: Expression, vars: Seq[Variable]): (Array[Int], Int) = {
    val idxMap = vars.zipWithIndex.toMap //bad when there is a lot of variables (10k) ...
    decomposeVector(e, idxMap)
  }
  
  def recompose(pos: List[Variable], neg: List[Variable], cst: Constant): Expression = {
    if (pos.isEmpty) {
      ((cst: Expression) /: neg)(Minus(_, _))
    } else {
      val posTerm = (pos: List[Expression]).reduceLeft(Plus(_, _))
      val negTerm = (posTerm /: neg)(Minus(_, _))
      if (cst.i == 0) negTerm
      else Plus(negTerm, cst)
    }
  }

  def recompose(pos: List[Variable], cst: Constant): Expression = {
    recompose(pos, Nil, cst)
  }
  
  def recomposeVector(coeffs: Seq[Int], cst: Int, vars: Seq[Variable]): Expression = {
    assert(coeffs forall (_ >= 0) )
    val pos = for (i <- 0 until coeffs.length; j <- 0 until coeffs(i)) yield vars(i)
    val neg = for (i <- 0 until coeffs.length; j <- coeffs(i) until 0) yield vars(i)
    recompose(pos.toList, neg.toList, Constant(cst))
  }

  def simplify(e: Expression): Expression = {
    val vars = Expression.variables(e).toSeq
    val (p, c) = decomposeVector(e, vars)
    recomposeVector(p,c,vars)
  }

  //TODO lazyCopier
  def alpha(e: Expression, subst: Map[Variable,Expression]): Expression = e match {
    case Plus(l,r) => Plus(alpha(l, subst), alpha(r, subst)) 
    case Minus(l,r) => Minus(alpha(l, subst), alpha(r, subst)) 
    case c @ Constant(_) => c
    case v @ Variable(_) => subst.getOrElse(v, v)
  }

}

abstract class Condition
case class Eq(l: Expression, r: Expression) extends Condition
case class Lt(l: Expression, r: Expression) extends Condition
case class Leq(l: Expression, r: Expression) extends Condition
case class And(lst: List[Condition]) extends Condition
case class Or(lst: List[Condition]) extends Condition
case class Not(c: Condition) extends Condition
case class Literal(b: Boolean) extends Condition

object Condition {

  def priority(e: Condition): Int = e match {
    case Eq(_,_) | Lt(_,_) | Leq(_,_) => 30
    case And(_) => 11
    case Or(_) => 10
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
    case And(lst) =>  lst.map(needParenthesis(priority(e), _)).mkString(" && ")
    case Or(lst) =>  lst.map(needParenthesis(priority(e), _)).mkString(" || ")
    case Not(c) =>  "!" + needParenthesis(priority(e), c) 
    case Literal(b) => b.toString
  }

  def variables(c: Condition): Set[Variable] = c match {
    case Eq(l,r) => Expression.variables(l) ++ Expression.variables(r)
    case Lt(l,r) => Expression.variables(l) ++ Expression.variables(r)
    case Leq(l,r) => Expression.variables(l) ++ Expression.variables(r)
    case And(lst) => (Set[Variable]() /: lst)(_ ++ variables(_))
    case Or(lst) => (Set[Variable]() /: lst)(_ ++ variables(_))
    case Not(c) => variables(c)
    case Literal(_) => Set()
  }

  def nnf(c: Condition): Condition = {
    def process(c: Condition, negate: Boolean): Condition = c match {
      case e @ Eq(_,_) => if (negate) Not(e) else e
      case Lt(l,r) => if (negate) Leq(r,l) else Lt(l,r)
      case Leq(l,r) => if (negate) Lt(r,l) else Leq(l,r)
      case And(lst) =>
        val lst2 = lst map (process(_, negate))
        if (negate) Or(lst2) else And(lst2)
      case Or(lst) => 
        val lst2 = lst map (process(_, negate))
        if (negate) And(lst2) else Or(lst2)
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
    case And(lst) =>
      val lst2 = lst.view.map(simplify)
      val lst3 = lst2 flatMap getTopLevelClauses
      val lst4 = lst3 filterNot (_ == Literal(true))
      if (lst4.isEmpty) Literal(true)
      else if (lst4 contains Literal(false)) Literal(false)
      else And(lst4.toList) //TODO remove duplicates ?
    case Or(lst) =>
      val lst2 = lst.view.map(simplify)
      val lst3 = lst2 flatMap getTopLevelDisj
      val lst4 = lst3 filterNot (_ == Literal(false))
      if (lst4.isEmpty) Literal(false)
      else if (lst4 contains Literal(true)) Literal(true)
      else Or(lst4.toList) //TODO remove duplicates ?
    case Not(c1) =>
      nnf(Not(simplify(c1)))
  }
  
  //TODO lazyCopier
  def alpha(c: Condition, subst: Map[Variable,Expression]): Condition = c match {
    case Eq(l,r) => Eq(Expression.alpha(l, subst), Expression.alpha(r, subst))
    case Lt(l,r) => Lt(Expression.alpha(l, subst), Expression.alpha(r, subst))
    case Leq(l,r) => Leq(Expression.alpha(l, subst), Expression.alpha(r, subst))
    case And(lst) => And(lst.map(alpha(_, subst)))
    case Or(lst) => Or(lst.map(alpha(_, subst)))
    case Not(c) => Not(alpha(c, subst))
    case l @ Literal(_) => l
  }

  def getTopLevelClauses(c: Condition): Seq[Condition] = c match {
    case And(lst) => lst flatMap getTopLevelClauses
    case other => Seq(other)
  }
  
  def getTopLevelDisj(c: Condition): Seq[Condition] = c match {
    case Or(lst) => lst flatMap getTopLevelDisj
    case other => Seq(other)
  }

  def getLowerBounds(guard: Condition): Map[Variable, Int] = {
    def process(c: Condition): Seq[(Variable, Int)] = c match {
      case Eq(v @ Variable(_), Constant(c)) => Seq(v -> c)
      case Eq(Constant(c), v @ Variable(_)) => Seq(v -> c)
      case Leq(Constant(c), v @ Variable(_)) => Seq(v -> c)
      case Lt(Constant(c), v @ Variable(_)) => Seq(v -> (c+1))
      case And(lst) => lst flatMap process
      case _ => Seq()
    }
    (Map[Variable, Int]() /: process(guard))( (acc, lb) => {
      if (acc contains lb._1) acc + (lb._1 -> math.max(acc(lb._1), lb._2))
      else acc + lb
    })
  }

  def getUpperBounds(guard: Condition): Map[Variable, Int] = {
    def process(c: Condition): Seq[(Variable, Int)] = c match {
      case Eq(v @ Variable(_), Constant(c)) => Seq(v -> c)
      case Eq(Constant(c), v @ Variable(_)) => Seq(v -> c)
      case Leq(v @ Variable(_), Constant(c)) => Seq(v -> c)
      case Lt(v @ Variable(_), Constant(c)) => Seq(v -> (c-1))
      case And(lst) => lst flatMap process
      case _ => Seq()
    }
    (Map[Variable, Int]() /: process(guard))( (acc, lb) => {
      if (acc contains lb._1) acc + (lb._1 -> math.min(acc(lb._1), lb._2))
      else acc + lb
    })
  }


}
