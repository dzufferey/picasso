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
  
  /** returns a substitution that can be used to subtitute the internal variables. */
  def substForRelation(substPre: Map[Variable, Variable], substPost: Map[Variable, Variable]) = {
    substPre.map{ case (a,b) => (preVars(a), b) } ++ substPost.map{ case (a,b) => (postVars(a), b) }
  }

  /** when the pre/post variables are disjoint, returns the relation over those variables.
   *  when the pre/post variables are not disjoint, you need to first rename the variables.*/
  def relationOverPrePost = {
    Logger.assert( (domain intersect range).isEmpty, "model.integer", "relationOverPrePost -> pre+post are not disjoint")
    putPre(putPost(relation))
  }
  
  def guardOverPrePost = {
    Logger.assert( (domain intersect range).isEmpty, "model.integer", "guardOverPrePost -> pre+post are not disjoint")
    putPre(putPost(guard))
  }

  def updatesOverPrePost = {
    Logger.assert( (domain intersect range).isEmpty, "model.integer", "updatesOverPrePost -> pre+post are not disjoint")
    putPre(putPost(updates))
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

  protected def keepOnlyPre(v: Variable) = {
    import picasso.math.hol._
    import picasso.math.qe._
    val vars = (iDomain - v).map(ToMathAst.variable)
    val v2 = ToMathAst.variable(v)
    val guardF = ToMathAst(guard)
    val query = Exists(vars.toList, guardF)
    LIA.qe(Set[Variable](), Set(v2), query) match {
      case Some(f2) =>
        val asCond = FromMathAst(f2)
        Logger("model.interger", LogDebug, "Transition.keepOnlyPre, QE returned: " + asCond)
        Some(asCond)
      case None => None
    }
  }

  protected def checkIfConstant(c: Condition): Map[Variable, Int] = {
    val clauses = Condition.getTopLevelClauses(c).view
    val eqClauses = clauses.flatMap{ case eq @ Eq(_,_) => Some(eq) case _ => None }
    val singleVarClause = eqClauses.filter( c => Condition.variables(c).size == 1 )
    val varCstPairs = singleVarClause.flatMap{ case eq @ Eq(e1, e2) =>
      val (p1,n1,c1) = Expression.decomposePosNeg(e1)
      val (p2,n2,c2) = Expression.decomposePosNeg(e2)
      val coeffTmp = p1.size - n1.size - p2.size + n2.size
      val cstTmp = c2.i - c1.i
      val (coeff,cst) = if (coeffTmp < 0) (-coeffTmp, -cstTmp) else (coeffTmp, cstTmp)
      if (coeff == 0) None
      else if (cst % coeff == 0) {
        Some((Condition.variables(eq).head, cst / coeff))
      } else {
        Logger("model.integer", LogWarning, "Transition.checkIfConstant, cannot divide " + cst + " by " + coeff + " in " + eq)
        None
      }
    }
    (Map[Variable, Int]() /: varCstPairs)( (acc, varCst) => {
      val (v,c) = varCst
      if (acc contains v) {
        Logger.assert(c == acc(v), "model.integer", v + " = " + c + " = " + acc(v))
        acc
      } else {
        acc + (v -> c)
      }
    })
  }

  //variables that have a constsant value
  lazy protected val iConstantVariable: Map[Variable, Int] = {
    //TODO can we express the cst var a SMT/QE query ?

    //for output it is about universally quantifying the input and QE
    val outputCst = quantifyAwayPreVars map checkIfConstant getOrElse Map[Variable, Int]()

    //for the input -> renaming and asking whether two version of the same var can be different ?
    //TODO using call to prover (keepOnlyPre)
    val inputCst = checkIfConstant(guard)

    //to test for uniqueness of the value it can take:
    //fresh iDomain -> for each v, isValid: guard /\ guard.alpha -> v = v.alpha
    //to know that: eliminate all the others variable and look what is left ?

    outputCst ++ inputCst
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
      Condition.simplify(Condition.alpha(relation, subst)),
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
      Condition.simplify(Condition.alpha(relation, csts.mapValues( i => Constant(i) ))),
      comment
    )
  }

  //TODO about sinks

  protected def iConeOfInfluence: Map[Variable,Set[Variable]] = {
    val clauses = Condition.getTopLevelClauses(relation)
    val clausesVars = clauses.map( cl => Condition.variables(cl) )
    val cones = for(v <- iDomain) yield {
      v -> clausesVars.filter(_ contains v).flatten.filter(iRange).toSet
    }
    cones.toMap
  }

  def coneOfInfluence: Map[Variable,Set[Variable]] = {
    iConeOfInfluence.map{ case (k,vs) => (toPre(k), vs.map(toPost)) }
  }
  
  protected def iVariablesBounds(pre: Map[Variable,(Option[Int],Option[Int])]): Map[Variable,(Option[Int],Option[Int])] = {
    //TODO how to substitute lower/higher to get correct bounds ?
    //we could use an ILP solver to minimize/maximize ?
    sys.error("TODO")
  }
  
  def variablesBounds(pre: Map[Variable,(Option[Int],Option[Int])]): Map[Variable,(Option[Int],Option[Int])] = {
    val pre2 = pre.map{ case (a,b) => (preVars(a), b) }
    val bounds = iVariablesBounds(pre2)
    bounds.map{ case (a, b) => (toPost(a), b) }
  }
  
  //TODO prune assume, i.e. simplify the relation

}


object Transition2 extends PartialOrdering[Transition2] {

  //match pre/post, then test is rel_1 -> rel_2 is valid.
  def lteq(t1: Transition2, t2: Transition2): Boolean = {
    val range = t1.range ++ t2.range
    val postSubst = range.iterator.map( v => (v, Variable(Namer("X_")))).toMap
    val t1p = t1.alphaPost(postSubst)
    val t2p = t2.alphaPost(postSubst)
    val rel1 = t1p.relationOverPrePost
    val rel2 = t2p.relationOverPrePost
    import picasso.math.hol._
    import picasso.math.qe._
    val univ = (t1.domain ++ t2.domain ++ t1p.range ++ t2p.range).map(ToMathAst.variable)
    val f1 = ToMathAst(rel1)
    val f2 = ToMathAst(rel2)
    val query = Application(Implies, List(f1, f2))
    LIA.valid(univ, Set[Variable](), query) match {
      case Some(b) => b
      case None =>
        Logger("model.integer", LogWarning, "Transition.lteq cannot prove that t1 \\subseteq t2")
        false
    }
  }

  def tryCompare(t1: Transition2, t2: Transition2): Option[Int] = {
    (lteq(t1, t2), lteq(t2, t1)) match {
      case (true, true) => Some(0)
      case (true, false) => Some(-1)
      case (false, true) => Some(1)
      case (false, false) => None
    }
  }

  protected def convertStmt(s: Statement): Condition = s match {
    case Transient(v) => Logger.logAndThrow("model.integer", LogError, "convertStmt -> found Transient -> TODO \\exists")
    case Relation(_new, _old) => Eq(_new, _old)
    case Skip => Literal(true)
    case Assume(c) => c
    case Variance(v1, v2, true, true) => Lt(v2, v1)
    case Variance(v1, v2, true, false) => Leq(v2, v1)
    case Variance(v1, v2, false, true) => Lt(v1, v2)
    case Variance(v1, v2, false, false) => Leq(v1, v2)
  }

  def apply(t: Transition): Transition2 = {
    val preVars = t.readVariables.iterator.map( v => (v, Variable(Namer("X_")))).toMap
    val postVars = t.updatedVars.iterator.map( v => (v, Variable(Namer("X_")))).toMap
    val t2 = t.alphaPre(preVars).alphaPost(postVars)
    val stmts = t2.updates.map(convertStmt)
    val relation = Condition.simplify((t2.guard /: stmts)(And(_,_)))
    new Transition2(
      t2.sourcePC,
      t2.targetPC,
      preVars,
      postVars,
      relation,
      t2.comment
    )
  }

  //compact using QE
  def compact(trs: Seq[Transition2]): Seq[Transition2] = {
    for (i <- 0 until (trs.length -1) ) {
      Logger.assert(trs(i).targetPC == trs(i+1).sourcePC, "model.integer", "Transition.compact: " + trs)
    }
    if (trs.length <= 1) {
      trs
    } else {
      //-create substitutions for the variables (SSA)
      val preVars = (trs map (_.domain)) :+ Set[Variable]()
      val postVars = Set[Variable]() +: (trs map (_.range))
      val vars = (preVars zip postVars) map {case (a,b) => a ++ b}
     
      val dict1 = scala.collection.mutable.HashMap[Variable, Variable]()
      val dict2 = scala.collection.mutable.HashMap[Variable, Variable]()
      var cnt = 0
      val dicts = for (vs <- vars) yield {
        (Map[Variable, Variable]() /: vs)( (acc, v) => {
          val newVar = Variable("X_" + cnt)
          cnt += 1
          acc + (v -> newVar)
        })
      }
      val ssa = trs.zip( dicts.sliding(2).toIterable ).map{ case (t, slide) => t.alphaPre(slide(0)).alphaPost(slide(1)) }
      
      import picasso.math.hol._
      import picasso.math.qe._
     
      def collectDijs(f: Formula): Seq[Formula] = f match {
        case Application(Or, args) => args flatMap collectDijs
        case other => Seq(other)
      }
     
      //-translate guards and updates to math.hol and make the query
      val hyp = ssa.head.guardOverPrePost
      val hypF = ToMathAst(hyp)
      val part1 = ssa.head.updatesOverPrePost
      val cstr = Application(And, ToMathAst(part1) :: ssa.tail.map(t => ToMathAst(t.relationOverPrePost)).toList)
      val query = Application(Implies, List(hypF, cstr))
     
      //-try to quantify away the intermediate variables
      val univ = dicts.head.values.map(ToMathAst.variable).toSet
      val exists = dicts.last.values.map(ToMathAst.variable).toSet
      val toEliminate = dicts.tail.init.flatMap(_.values).map(ToMathAst.variable)
      val f = Exists(toEliminate.toList, query)
      LIA.qe(univ, exists, f) match {
        case Some(f2) =>
          //remove the negated assumption that are part of f2 to keep only the new update cstr
          val disj = collectDijs(f2)
          val valid = disj.filter(d => LIA.valid(univ, exists, Application(Implies, List(hypF, d)) ).getOrElse(true) )
          val f3 =
            if (valid.isEmpty) Logger.logAndThrow("model.integer", LogError, "compact, no valid disjunct")
            else if (valid.size == 1) valid.head
            else Application(Or, valid.toList)
          //-back to model.integer.AST
          val asCond = FromMathAst(f3)
          Logger("model.integer", LogDebug, "compact, QE returned: " + asCond)
          val t2 = new Transition2(
            trs.head.sourcePC,
            trs.last.targetPC,
            dicts.head,
            dicts.last,
            picasso.model.integer.And(hyp, asCond),
            trs.map(_.comment).mkString("; ")
          )
          Seq(t2)
        case None =>
          trs
      }
    }
  }

}
