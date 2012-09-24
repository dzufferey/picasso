package picasso.model.integer

import picasso.utils._
import picasso.graph._

class Transition2(val sourcePC: String,
                 val targetPC: String,
                 val preVars: Map[Variable, Variable],
                 val postVars: Map[Variable, Variable],
                 val relation: Condition,
                 val comment: String = "") extends picasso.math.Transition[State] {

  //TODO do we want a normal form ?

  lazy val toPre = preVars.map{ case (a,b) => (b,a) }
  lazy val toPost = postVars.map{ case (a,b) => (b,a) }

  lazy val domain: Set[Variable] = preVars.keySet
  lazy val range: Set[Variable] = postVars.keySet
  lazy val variables: Set[Variable] = domain ++ range
  
  //internal variables
  lazy val iDomain: Set[Variable] = preVars.keySet
  lazy val iRange: Set[Variable] = postVars.keySet
  lazy val iVariables: Set[Variable] = domain ++ range

  //sanity checks
  Logger.assert(Condition.variables(relation).subsetOf(iVariables), "model.integer", "not closed: " + this)
  Logger.assert((iDomain intersect iRange).isEmpty, "model.integer", "internal variables conflict " + this)
  Logger.assert(noDisj(relation), "model.integer", "contains disjunction: " + this)

  private def noDisj(c: Condition): Boolean = c match {
    case Or(_, _) => false
    case And(l, r) => noDisj(l) && noDisj(r)
    case Not(n) => noConj(n)
    case _ => true
  }
  
  private def noConj(c: Condition): Boolean = c match {
    case And(_, _) => false
    case Or(l, r) => noDisj(l) && noDisj(r)
    case Not(n) => noDisj(n)
    case _ => true
  }

  def isWellDefined = {
    import picasso.math.hol._
    import picasso.math.qe._
    val univ = iDomain.map(ToMathAst.variable)
    val exists = iRange.map(ToMathAst.variable)
    val guardF = ToMathAst(guard)
    val updatesF = ToMathAst(updates)
    val query = Application(Implies, List(guardF, updatesF))
    LIA.valid(univ, exists, query) match {
      case Some(b) => b
      case None =>
        Logger("model.integer", LogWarning, "cannot prove that t is well-defined where t = " + this)
        false
    }
  }

  override def toString = {
    "Transition(" + sourcePC +
             ", " + targetPC +
             ", " + preVars.map{ case (a,b) => Expression.print(a) + "->" + Expression.print(b) }.mkString("{",", ","}") +
             ", " + postVars.map{ case (a,b) => Expression.print(a) + "->" + Expression.print(b) }.mkString("{",", ","}") +
             ", " + Condition.print(relation) +
             ", \"" + comment + "\")"
  }
  
  def apply(s: State): Set[State] = {
    sys.error("TODO: for the moment the analysis of interger program is shipped to other tool")
  }

  def isDefinedAt(s: State): Boolean = {
    sourcePC == s.pc
  }

  protected def putPre(c: Condition) = Condition.alpha(c, toPre)
  protected def putPost(c: Condition) = Condition.alpha(c, toPost)

  def guard: Condition = {
    val clauses = Condition.getTopLevelClauses(relation)
    val onlyPre = clauses.filter(c => Condition.variables(c) subsetOf iDomain)
    val combined = ((Literal(true): Condition) /: onlyPre)(And(_, _))
    Condition.simplify(combined)
  }

  def updates: Condition = {
    val clauses = Condition.getTopLevelClauses(relation)
    val notOnlyPre = clauses.filter(c => !Condition.variables(c).subsetOf(iDomain))
    val combined = ((Literal(true): Condition) /: notOnlyPre)(And(_, _))
    Condition.simplify(combined)
  }

  def alpha(subst: Map[Variable, Variable]) = {
    new Transition2(
      sourcePC,
      targetPC,
      preVars.map{ case (k,v) => (subst.getOrElse(k,k), v)},
      postVars.map{ case (k,v) => (subst.getOrElse(k,k), v)},
      relation,
      comment
    )
  }

  def alphaPre(subst: Map[Variable, Variable]) = {
    new Transition2(
      sourcePC,
      targetPC,
      preVars.map{ case (k,v) => (subst.getOrElse(k,k), v)},
      postVars,
      relation,
      comment
    )
  }
  
  def alphaPost(subst: Map[Variable, Variable]) = {
    new Transition2(
      sourcePC,
      targetPC,
      preVars,
      postVars.map{ case (k,v) => (subst.getOrElse(k,k), v)},
      relation,
      comment
    )
  }
  
  def freshInternal(n: Namer = Namer): Transition2 = {
    val subst = iVariables.iterator.map( v => v -> Variable(n("X_")) ).toMap
    new Transition2(
      sourcePC,
      targetPC,
      preVars.map{ case (k,v) => (k, subst.getOrElse(v,v)) },
      postVars.map{ case (k,v) => (k, subst.getOrElse(v,v)) },
      Condition.alpha(relation, subst),
      comment
    )
  }

  protected def quantifyAwayPreVars = {
    import picasso.math.hol._
    import picasso.math.qe._
    val univ = iDomain.map(ToMathAst.variable)
    val exists = iRange.map(ToMathAst.variable)
    val guardF = ToMathAst(guard)
    val updatesF = ToMathAst(updates)
    val queryBody = Application(Implies, List(guardF, updatesF))
    val query = ForAll(univ.toList, queryBody)
    LIA.qe(Set[Variable](), exists, query) match {
      case Some(f2) =>
        val asCond = FromMathAst(f2)
        Logger("model.interger", LogDebug, "Transition.quantifyAwayPreVars, QE returned: " + asCond)
        Some(asCond)
      case None => None
    }
  }

  protected def keepOnlyPre(v: Variable): Condition = {
    val vars = (iDomain - v).map(ToMathAst.variable)
    val v2 = ToMathAst.variable(v)
    val guardsF = ToMathAst(guard)
    sys.error("TODO")
  }

  //variables that have a constsant value
  lazy protected val iConstantVariable: Map[Variable, Int] = {
    //TODO can we express the cst var a SMT/QE query ?

    //for output it is about universally quantifting the input and QE
    //TODO use the output of quantifyAwayPreVars

    //for the input -> renaming and asking whether two version of the same var can be different ?
    //TODO to test for uniqueness of the value it can take:
    //fresh iDomain -> for each v, isValid: guard /\ guard.alpha -> v = v.alpha
    //to know that: eliminate all the others variable and look what is left ?
    sys.error("TODO")
  }

  //returns the post vars that get a constant value
  def constantVariables: Map[Variable, Int] = {
    val csts = iConstantVariable.filterKeys(iRange)
    csts.map{ case (v, c) => (toPost(v), c) }
  }

  def propagteInputConstants(csts: Map[Variable, Int]) = {
    val subst = csts.flatMap{ case (v,c) => preVars.get(v).map( v2 => v2 -> Constant(c)) }
    new Transition2(
      sourcePC,
      targetPC,
      preVars -- csts.keys,
      postVars,
      Condition.alpha(relation, subst),
      comment
    )
  }

  def propagteOutputConstants(vars: Set[Variable]) = {
    val vars2 = vars map postVars
    val csts = iConstantVariable.filterKeys(iRange)
    Logger.assert( vars2 subsetOf csts.keySet, "model.integer", "propagting some non-contant terms")
    new Transition2(
      sourcePC,
      targetPC,
      preVars,
      postVars -- vars,
      Condition.alpha(relation, csts.mapValues( i => Constant(i) )),
      comment
    )
  }

  //TODO about sinks

  protected def coneOfInfluence: Map[Variable,Set[Variable]] = {
    sys.error("TODO")
  }
  
  def variablesBounds(pre: Map[Variable,(Option[Int],Option[Int])]): Map[Variable,(Option[Int],Option[Int])] = {
    sys.error("TODO")
  }
  
  //TODO prune assume, i.e. simplify the relation

}

object Transition2 {

  //TODO compact using QE

}
