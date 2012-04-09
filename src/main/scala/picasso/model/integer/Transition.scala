package picasso.model.integer

import picasso.utils._

class Transition(val sourcePC: String,
                 val targetPC: String,
                 val guard: Condition,
                 val updates: Seq[Statement],
                 val comment: String = "") extends picasso.math.Transition[State] {

  override def toString = {
    "Transition(" + sourcePC +
             ", " + targetPC +
             ", " + Condition.print(guard) +
             ", " + updates.map(Statement.print).mkString("{ ", "; ", "}") +
             ", \"" + comment + "\")"
  }
  
  def apply(s: State): Set[State] = {
    sys.error("TODO: for the moment the analysis of interger program is shipped to other tool")
  }

  def isDefinedAt(s: State): Boolean = {
    sourcePC == s.pc
  }

  def variables: Set[Variable] = {
    val updatesAll = (Set[Variable]() /: updates)(_ ++ Statement.getAllVariables(_))
    val updatesTransient = (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
    Condition.variables(guard) ++ updatesAll -- updatesTransient
  }

  /** the variables of this transition as a fixed sequence.
   *  (useful for pretty printing) */
  lazy val sequencedVariable: Seq[Variable] = variables.toSeq

  def guardVariables = Condition.variables(guard)

  def transientVariables: Set[Variable] = {
    (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
  }

  def updatedVars: Set[Variable] = {
    val updated = (Set[Variable]() /: updates)(_ ++ Statement.getUpdatedVars(_))
    val transient = (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
    updated -- transient
  }
    
  //is not exact but a superset
  def assignedToNonZero(preNonZero: Set[Variable] = Set()): Set[Variable] = {
    val nonZeros = updates.flatMap{
      case Relation(lhs, rhs) =>
        val (pos, neg, cst) = Expression.decompose(rhs)
        val pos2 = pos.filter(preNonZero)
        val neg2 = neg.filter(preNonZero)
        if (pos.isEmpty && neg.isEmpty && cst.i == 0) Set()
        else Expression.variables(lhs)
      case _ => None
    }
    val nz = nonZeros.toSet
    assert(nz subsetOf updatedVars)//check that no transient has been caught
    nz
  }
  
  //is not exact but a subset
  def assignedToZero(preNonZero: Set[Variable] = Set()): Set[Variable] = {
    val zeros = updates.flatMap{
      case Relation(v1 @ Variable(_), rhs) =>
        val (pos, neg, cst) = Expression.decompose(rhs)
        val pos2 = pos.filter(preNonZero)
        val neg2 = neg.filter(preNonZero)
        if (pos.isEmpty && neg.isEmpty && cst.i == 0) Some(v1)
        else None
      case _ => None
    }
    zeros.toSet
  }

  def alpha(subst: Map[Variable, Expression]) = {
    val guard2 = Condition.alpha(guard, subst)
    val updates2 = updates map ( Statement.alpha(_, subst) )
    new Transition(sourcePC, targetPC, guard2, updates2, comment)
  }

  def alphaPre(subst: Map[Variable, Expression]) = {
    val guard2 = Condition.alpha(guard, subst)
    val updates2 = updates map ( Statement.alphaPre(_, subst) )
    new Transition(sourcePC, targetPC, guard2, updates2, comment)
  }
  
  def alphaPost(subst: Map[Variable, Expression]) = {
    val updates2 = updates map ( Statement.alphaPost(_, subst) )
    new Transition(sourcePC, targetPC, guard, updates2, comment)
  }

  /** given equals variable (equivalence classes),
   *  returns the set of variable that are equal afterward.
   *  This is not exact but a refinement of the actual equivalence classes.
   */
  def equivalenceClasses(preEqClasses: Set[Set[Variable]], nonZeros: Map[String, Set[Variable]]): Set[Set[Variable]] = {
    var subst = preEqClasses.toSeq.flatMap( set => set.map(x => (x -> set.head)) ).toMap
    val updates2 = updates map ( Statement.alphaPre(_, subst) )
    val simpleUpdates = updates2 flatMap (s => s match {
      case Affect(v, rhs) => Some(v -> Expression.decompose(rhs))
      case Relation(Plus(v @ Variable(_), Constant(c)), rhs) =>
        val (p,n,c2) = Expression.decompose(rhs)
        Some(v -> (p,n,Constant(c2.i - c)))
      case _ => None
    })
    val knowledge = preEqClasses.flatten
    val byUpdate = simpleUpdates.groupBy(_._2).map{ case (k, v) => (k, v.map{_._1}.toSet) }
    val tv = transientVariables
    val informedChoice = byUpdate.filterKeys{ case (pos, neg, cst) => 
      val vars = pos ++ neg
      vars forall (v => knowledge(v) || tv(v) )
    }
    val newClasses = informedChoice.values.toSet
    val uv = updatedVars
    //the frame is the variables that are not updated
    val frame = preEqClasses.map( _.filterNot(uv contains) ).filterNot(_.isEmpty)
    val simplyUpdated = simpleUpdates.map(_._1).toSet
    val unknown = uv.filterNot(v => simplyUpdated contains v).map(v => Set(v))
    //use the knowledge of the zero values
    val allVars = knowledge ++ uv
    val zeros = allVars -- nonZeros(targetPC)
    val res = frame ++ newClasses ++ unknown
    val (zeroUpdate, nonZeroUpdate) = res.partition(_ exists zeros)
    val res2 = nonZeroUpdate + zeroUpdate.flatten
    //TODO connection between old an new variables (more than just the 0 case)
    //println("XXX: " + this)
    //println("XXX: knowledge: " + knowledge.map(_.name).mkString(", "))
    //println("XXX: byUpdate\n" + byUpdate.mkString("\n"))
    //println("XXX: informedChoice\n" + informedChoice.mkString("\n"))
    //println("XXX: updated vars: " + uv.mkString(", "))
    //println("XXX: simple updates: " + simpleUpdates.map(_._1).mkString(", "))
    //println("XXX: unknown: " + unknown.mkString(", "))
    //println("XXX: before " + preEqClasses)
    //println("XXX: after " + res2)
    res2
  }
  
  //TODO can we have a method to eliminate the transient vars ?
  //as a special case of quantifier elimination ?
  //transient vars are used to preserve some difference between primed and unprimed

  /** Remove unneeded/unchanged variables */
  def leaner: Transition = {
    val guard2 = Condition.simplify(guard)
    val updates2 = updates.map(Statement.simplify)
    val (changing, notChanging) = updates2.partition{
      case Relation(Variable(v1), Variable(v2)) => v1 != v2
      case _ => true
    }
    //the variables that stays constant
    val notChangingVars = notChanging.map{case Affect(v1, v2) => v1}.toSet
    //the variable needed for some other transition
    val neededForGuard = Condition.variables(guard2)
    val transient = transientVariables
    val neededForChanging = (Set[Variable]() /: changing)(_ ++ Statement.getAllVariables(_))
    val toRemove = notChangingVars -- neededForGuard -- transient -- neededForChanging
    val updates3 = updates2.filter{ case Affect(v1, v2) => v1 != v2 || !toRemove(v1) case _ => true }
    val t2 = new Transition(sourcePC, targetPC, guard2, updates3, comment)
    assert((t2.variables intersect toRemove).isEmpty)
    t2
  }

  /** Return a transitions s.t. only one variable is used for the group 
   *  This method assumes that only one variable of the group can be nonZeros at the time (except for the initial state).
   */
  def mergeVariables(group: Set[Variable], newVar: Variable): Transition = {
    //need to look which var is assigned to 0:
    val anz = assignedToNonZero().filter(group contains _)
    //println("XXX tr: " + this)
    //println("XXX group: " + group)
    //println("XXX newVar: " + newVar)
    //println("XXX anz: " + anz)
    assert(anz.size <= 1)

    def mergeInExpression(e: Expression): Expression = {
      val (pos, neg, cst) = Expression.decompose(e)
      if (pos.exists(group contains _)) {
        assert(! neg.exists(group contains _))
        val pos2 = newVar :: pos.filterNot(group contains _)
        Expression.recompose(pos2, neg, cst)
      } else if (neg.exists(group contains _)) {
        val neg2 = newVar :: neg.filterNot(group contains _)
        Expression.recompose(pos, neg2, cst)
      } else {
        Expression.recompose(pos, neg, cst)
      }
    }
 
    //TODO there should be some more sanity checks ?
    def mergeInCondition(c: Condition): Condition = c match {
      case Eq(l,r) => Eq(mergeInExpression(l), mergeInExpression(r))
      case Lt(l,r) => Lt(mergeInExpression(l), mergeInExpression(r))
      case Leq(l,r) => Leq(mergeInExpression(l), mergeInExpression(r))
      case And(l,r) => And(mergeInCondition(l), mergeInCondition(r))
      case Or(l,r) => Or(mergeInCondition(l), mergeInCondition(r))
      case Not(c) => Not(mergeInCondition(c))
      case l @ Literal(_) => l
    }

    //look at all the left hand side, gather the ones with the variables in group
    //TODO checks that they are not involved with something else ...
    val (thingsThatMatter, affectingOther) = updates.partition(s => Statement.getUpdatedVars(s).exists(group contains _))
    val (affectThatMatter, assumeThatMatters) = thingsThatMatter.partition{ case Relation(_,_) => true case _ => false }
    val (lhsAcc, rhsAcc) = ((Constant(0): Expression, Constant(0): Expression) /: affectThatMatter)( (acc, stmt) => stmt match {
      case Relation(x, y) => (Plus(x, acc._1), Plus(y, acc._2))
      case other => Logger.logAndThrow("integer.Transition", LogError, "Expected Relation, found: " + other)
    })
    val mergedAffect = Relation(mergeInExpression(lhsAcc), mergeInExpression(rhsAcc))
    val mergedAssumes = assumeThatMatters map {
      case Assume(c) => Statement.simplify(Assume(mergeInCondition(c)))
      case vr @ Variance(v1, v2, _, _) =>
        assert(group(v1) || group(v2));
        Logger("integer.Transition", LogWarning, "mergeVariables changing: " + vr + ", dropping the constraint")
        Skip
      case other => Logger.logAndThrow("integer.Transition", LogError, "Expected Assume or Variance, found: " + other)
    }
    val affectingOtherMerged = affectingOther.map{
      case Relation(x, y) =>
        assert(Expression.variables(x).forall(v => !group.contains(v)))
        Relation(x, mergeInExpression(y))
      case a @ Assume(c) =>
        assert(Condition.variables(c).forall(v => !group.contains(v)))
        a
      case vr @ Variance(v1, v2, _, _) =>
        assert(!group(v1))
        if (group(v2)) {
          Logger("integer.Transition", LogWarning, "mergeVariables changing: " + vr + ", dropping the constraint")
          Skip
        } else {
          vr
        }
      case other => other
    }
    
    val guard2 = mergeInCondition(guard)
    //println("XXX guard2: " + guard2)
    val updates2 = mergedAffect +: (mergedAssumes ++ affectingOtherMerged)
    //println("XXX updates2: " + updates2)

    val t2 = new Transition(sourcePC, targetPC, guard2, updates2, comment)
    t2.leaner
  }


}

object Transition {

  //try to remove intermediate state (substitution / constrains propagation) while preserving the termination
  def compact(trs: Seq[Transition]): Seq[Transition] = {
    for (i <- 0 until (trs.length -1) ) {
      assert(trs(i).targetPC == trs(i+1).sourcePC)
    }
    //substitution are easy and can be used for affectation
    //for equalities -> projection using an LP solver ?! 
    sys.error("TODO")
  }

}
