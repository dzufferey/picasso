package picasso.model.integer

import picasso.utils._
import picasso.graph._

//implicit assumption that we are working with natural number (counters), not integers
class Transition(val sourcePC: String,
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
  lazy val iDomain: Set[Variable] = toPre.keySet
  lazy val iRange: Set[Variable] = toPost.keySet
  lazy val iVariables: Set[Variable] = iDomain ++ iRange

  //sanity checks
  Logger.assert(Condition.variables(relation).subsetOf(iVariables), "model.integer", "not closed: " + this)
  Logger.assert((iDomain intersect iRange).isEmpty, "model.integer", "internal variables conflict " + this)
  Logger.assert(noDisj(relation), "model.integer", "contains disjunction: " + relation)

  private def noDisj(c: Condition): Boolean = c match {
    case Or(_) => false
    case And(lst) => lst forall noDisj
    case Not(n) => noConj(n)
    case _ => true
  }
  
  private def noConj(c: Condition): Boolean = c match {
    case And(_) => false
    case Or(lst) => lst forall noConj
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
    val combined = And(onlyPre.toList)
    Condition.simplify(combined)
  }

  def updates: Condition = {
    val clauses = Condition.getTopLevelClauses(relation)
    val notOnlyPre = clauses.filter(c => !Condition.variables(c).subsetOf(iDomain))
    val combined = And( notOnlyPre.toList)
    Condition.simplify(combined)
  }
  
  /** returns a substitution that can be used to subtitute the internal variables. */
  def substForRelation[A](substPre: Map[Variable, A], substPost: Map[Variable, A]) = {
    val s1 = substPre.flatMap{ case (a,b) => preVars.get(a).map{ a2 => a2 -> b } }
    val s2 = substPost.flatMap{ case (a,b) => postVars.get(a).map{ a2 => a2 -> b } }
    s1 ++ s2
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
    new Transition(
      sourcePC,
      targetPC,
      preVars.map{ case (k,v) => (subst.getOrElse(k,k), v)},
      postVars.map{ case (k,v) => (subst.getOrElse(k,k), v)},
      relation,
      comment
    )
  }

  def alphaPre(subst: Map[Variable, Variable]) = {
    new Transition(
      sourcePC,
      targetPC,
      preVars.map{ case (k,v) => (subst.getOrElse(k,k), v)},
      postVars,
      relation,
      comment
    )
  }
  
  def alphaPost(subst: Map[Variable, Variable]) = {
    new Transition(
      sourcePC,
      targetPC,
      preVars,
      postVars.map{ case (k,v) => (subst.getOrElse(k,k), v)},
      relation,
      comment
    )
  }
  
  def freshInternal(n: Namer = Namer): Transition = {
    val subst = iVariables.iterator.map( v => v -> Variable(n("X_")) ).toMap
    new Transition(
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
    val toRemove = iDomain.map(ToMathAst.variable)
    val toKeep = iRange.map(ToMathAst.variable)
    val guardF = ToMathAst(guard)
    val updatesF = ToMathAst(updates)
    val queryBody = Application(And, List(guardF, updatesF))
    val query = Exists(toRemove.toList, queryBody)
    LIA.qe(Set[Variable](), toKeep, query) match {
      case Some(f2) =>
        val asCond = FromMathAst(f2)
        Logger("model.interger", LogDebug, "Transition.quantifyAwayPreVars, QE returned: " + asCond)
        Some(asCond)
      case None => None
    }
  }

  protected def checkIfConstant(c: Condition): Map[Variable, Int] = {
    //TODO can we express the cst var a SMT/QE query ?
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
      //Logger("model.interger", LogDebug, "Transition.checkIfConstant: " + v + " = " + c)
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
    //for output it is about universally quantifying the input and QE
    val outputCst = quantifyAwayPreVars map checkIfConstant getOrElse Map[Variable, Int]()
    //for the input -> renaming and asking whether two version of the same var can be different ?
    //val inputCst = checkIfConstant(guard)
    outputCst// ++ inputCst
  }

  //returns the post vars that get a constant value
  def constantVariables: Map[Variable, Int] = {
    val csts = iConstantVariable//.filterKeys(iRange)
    val outCsts = csts.map{ case (v, c) => (toPost(v), c) }
    Logger("model.interger", LogDebug, "Transition.constantVariables: " + outCsts.mkString(", ") )
    outCsts
  }

  def propagteInputConstants(csts: Map[Variable, Int]) = {
    val subst = substForRelation(csts.mapValues( i => Constant(i)), Map[Variable,Constant]())
    new Transition(
      sourcePC,
      targetPC,
      preVars -- csts.keys,
      postVars,
      Condition.simplify(Condition.alpha(relation, subst)),
      comment
    )
  }

  def propagteOutputConstants(vars: Set[Variable]) = {
    val vars2 = vars.flatMap(postVars.get)
    val csts = iConstantVariable.filterKeys(v => /*iRange(v) &&*/ vars2(v) )
    Logger.assert( vars2 subsetOf csts.keySet, "model.integer", "propagting some non-contant terms")
    new Transition(
      sourcePC,
      targetPC,
      preVars,
      postVars -- vars,
      Condition.simplify(Condition.alpha(relation, csts.mapValues( i => Constant(i) ))),
      comment
    )
  }

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

  def eliminateVariables(prefixes: Iterable[String]) = {
    val (toElim, toKeep) = variables.partition(v => prefixes exists v.name.startsWith)
    val iToElim = toElim.flatMap( v => List(preVars.get(v), postVars.get(v)).flatten)
    val iToKeep = toKeep.flatMap( v => List(preVars.get(v), postVars.get(v)).flatten)
    import picasso.math.hol._
    import picasso.math.qe._
    val query = ToMathAst(relation)
    val f = Exists(iToElim.map(ToMathAst.variable).toList, query)
    LIA.qe(Set(), iToKeep.map(ToMathAst.variable), f) match {
      case Some(f2) =>
        val asCond = FromMathAst(f2)
        Logger("model.integer", LogDebug, "eliminateVar, QE returned: " + asCond)
        val t2 = new Transition(
          sourcePC,
          targetPC,
          preVars -- toElim,
          postVars -- toElim,
          asCond,
          comment
        )
        t2
      case None =>
        this
    }
  }
  
  /*
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
  */
  
  //TODO prune assume, i.e. simplify the relation

  def unusedVariable: Set[Variable] = {
    (iDomain -- Condition.variables(relation)) map toPre
  }

  def unconstrainedVariables: Set[Variable] = {
    (iRange -- Condition.variables(relation)) map toPost
  }

}


object Transition extends PartialOrdering[Transition] {

  //match pre/post, then test is rel_1 -> rel_2 is valid.
  def lteq(t1: Transition, t2: Transition): Boolean = {
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

  def tryCompare(t1: Transition, t2: Transition): Option[Int] = {
    (lteq(t1, t2), lteq(t2, t1)) match {
      case (true, true) => Some(0)
      case (true, false) => Some(-1)
      case (false, true) => Some(1)
      case (false, false) => None
    }
  }

  /*
  protected def convertStmt(s: Statement): Condition = s match {
    case Relation(_new, _old) => Eq(_new, _old)
    case Skip => Literal(true)
    case Assume(c) => c
    case Variance(v1, v2, true, true) => Lt(v2, v1)
    case Variance(v1, v2, true, false) => Leq(v2, v1)
    case Variance(v1, v2, false, true) => Lt(v1, v2)
    case Variance(v1, v2, false, false) => Leq(v1, v2)
  }
  */

  /*
  def apply(t: Transition): Transition = {
    val preVars = t.readVariables.iterator.map( v => (v, Variable(Namer("X_")))).toMap
    val postVars = t.updatedVars.iterator.map( v => (v, Variable(Namer("X_")))).toMap
    val t2 = t.alphaPre(preVars).alphaPost(postVars)
    val guards = Condition.getTopLevelClauses(t2.guard)
    val stmts = t2.updates.map(convertStmt)
    val relation = Condition.simplify(And( (guards ++ stmts).toList ))
    val t3 = new Transition(
      t2.sourcePC,
      t2.targetPC,
      preVars,
      postVars,
      relation,
      t2.comment
    )
    Logger("model.integer", LogDebug, "t  = " + t)
    Logger("model.integer", LogDebug, "t' = " + t3)
    t3
  }
  */

  protected def ssa(trs: Seq[Transition]): (Seq[Map[Variable,Variable]], Seq[Transition]) = {
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
    val trs2 = trs.zip( dicts.sliding(2).toIterable ).map{ case (t, slide) => t.alphaPre(slide(0)).alphaPost(slide(1)) }
    (dicts, trs2)
  }

  //compact using QE
  def compact(trs: Seq[Transition]): Seq[Transition] = {
    for (i <- 0 until (trs.length -1) ) {
      Logger.assert(trs(i).targetPC == trs(i+1).sourcePC, "model.integer", "Transition.compact: " + trs)
    }
    if (trs.length <= 1) {
      trs
    } else {

      val (dicts, ssaed) = ssa(trs)
      
      import picasso.math.hol._
      import picasso.math.qe._
     
      //-translate guards and updates to math.hol and make the query
      val query = Application(And, ssaed.map(t => ToMathAst(t.relationOverPrePost)).toList)
     
      //-try to quantify away the intermediate variables
      val existsPre = dicts.head.values.map(ToMathAst.variable).toSet
      val existsPost = dicts.last.values.map(ToMathAst.variable).toSet
      val toEliminate = dicts.tail.init.flatMap(_.values).map(ToMathAst.variable)
      val f = Exists(toEliminate.toList, query)
      LIA.qe(Set(), existsPre ++ existsPost, f) match {
        case Some(f2) =>
          val asCond = FromMathAst(f2)
          Logger("model.integer", LogDebug, "compact, QE returned: " + asCond)
          val t2 = new Transition(
            trs.head.sourcePC,
            trs.last.targetPC,
            dicts.head,
            dicts.last,
            asCond,
            trs.map(_.comment).mkString("; ")
          )
          Seq(t2)
        case None =>
          trs
      }
    }
  }
  
  def candidateRankingFcts(cycle: Seq[Transition]): Iterable[Set[Variable]] = {
    Logger.assert(!cycle.isEmpty && cycle.head.sourcePC == cycle.last.targetPC, "model.integer", "not a cycle: " + cycle)
    //ssa
    val (dicts, ssaed) = ssa(cycle)
    val pre =  dicts.head
    val post = dicts.last
    Logger.assert(
      pre.keySet == post.keySet,
      "model.integer",
      "not the same variables?\n" + pre.keySet.mkString(", ") + "\n" + post.keySet.mkString(", ") + "\n" + cycle.mkString("\n")
    )
    //compose the transitions
    val composedRelation = ssaed.view.map(_.relationOverPrePost).toList

    val allVars = dicts.flatMap(_.values).toSet.map(ToMathAst.variable)
    
    //ask whether a variable is striclty decreasing
    def decrease(vars: Iterable[Variable]): Boolean = {
      val v1 = vars.map(v => pre(v): Expression).reduceLeft(Plus(_,_))
      val v2 = vars.map(v => post(v): Expression).reduceLeft(Plus(_,_))
      val query = And( Leq(v1, v2) :: composedRelation)
      picasso.math.qe.LIA.valid(Set(), allVars, ToMathAst(query)) match {
        case Some(b) => b
        case None =>
          Logger("model.integer", LogWarning, "Transition.candidateRankingFcts, cannot solve: " + query)
          false
      }
    }

    //TODO we need something faster and better quality !!

    val (decr, incr) = pre.keySet.partition(v => decrease(List(v)))
    val part1 = decr.subsets.flatMap(sub => if (sub.isEmpty) None else Some(sub)).toSeq

    //TODO incrementally
    def tryAdd(base: Set[Variable], candidates: Set[Variable]): Seq[Set[Variable]] = {
      val ok = candidates.filter(v => decrease(base + v))
      var suffixes = ok
      val recurse = ok.toSeq.flatMap(v => { suffixes -= v; tryAdd(base + v, suffixes)} )
      base +: recurse
    }

    part1.flatMap(tryAdd(_, incr))
  }

}
