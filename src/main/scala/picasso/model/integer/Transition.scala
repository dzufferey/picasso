package picasso.model.integer

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
  def assignedToNonZero: Set[Variable] = {
    val nonZeros = updates.flatMap{
      case Relation(lhs, rhs) if rhs != Constant(0) => Expression.variables(lhs)
      case _ => None
    }
    val nz = nonZeros.toSet
    assert(nz subsetOf updatedVars)//check that no transient has been caught
    nz
  }
  
  //is not exact but a subset
  def assignedToZero: Set[Variable] = {
    val zeros = updates.flatMap{
      case Relation(v1 @ Variable(_), Constant(0)) => Some(v1)
      case _ => None
    }
    zeros.toSet
  }

  def alpha(subst: Map[Variable, Expression]) = {
    val guard2 = Condition.alpha(guard, subst)
    val updates2 = updates map ( Statement.alpha(_, subst) )
    new Transition(sourcePC, targetPC, guard2, updates2, comment)
  }
  
  //TODO can we have a method to eliminate the transient vars ?
  //as a special case of quantifier elimination ?
  //transient vars are used to preserve some difference between primed and unprimed

  /** Remove unneeded/unchanged variables */
  def leaner: Transition = {
    val guard2 = Condition.simplify(guard)
    val (changing, notChanging) = updates.partition{
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
    val updates2 = updates.filter{ case Affect(v1, v2) => v1 != v2 || !toRemove(v1) case _ => true }
    val t2 = new Transition(sourcePC, targetPC, guard2, updates2, comment)
    assert((t2.variables intersect toRemove).isEmpty)
    t2
  }

  /** Return a transitions s.t. only one variable is used for the group 
   *  This method assumes that only one variable of the group can be nonZeros at the time (except for the initial state).
   */
  def mergeVariables(group: Set[Variable], newVar: Variable, nonZeros: Map[String, Set[Variable]]): Transition = {
    val liveBefore = nonZeros(sourcePC)
    val liveAfter = nonZeros(targetPC)
    val zeroBefore = group.filterNot( liveBefore contains _ )
    val zeroAfter = group.filterNot( liveAfter contains _ )
    //the first idea is replace the zero vars by zero
    val beforeSubst = zeroBefore.map(v => (v -> Constant(0))).toMap
    val guard2 = Condition.alpha(guard, beforeSubst)
    val updates2 = updates.map(Statement.alphaPre(_, beforeSubst))
    val afterSubst = zeroAfter.map(v => (v -> Constant(0))).toMap
    val updates3 = updates2.map(Statement.alphaPost(_, afterSubst))
    
    //then merge / replace what it left

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
        e
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
    
    //TODO there should be some more sanity checks ?
    def mergeInStatement(s: Statement): Statement = s match {
      case Relation(n, o) => Statement.simplify(Relation(mergeInExpression(n), mergeInExpression(o)))
      case Assume(c) => Statement.simplify(Assume(mergeInCondition(c)))
      case other => other
    }

    val t2 = new Transition(sourcePC, targetPC, mergeInCondition(guard2), updates3 map mergeInStatement, comment)
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
