package picasso.model.integer

class Transition(val sourcePC: String,
                 val targetPC: String,
                 val guard: Condition,
                 val updates: Seq[Statement],
                 val comment: String = "") extends picasso.math.Transition[State] {
  
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

  def transientVariables: Set[Variable] = {
    (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
  }

  def updatedVars: Set[Variable] = {
    val updated = (Set[Variable]() /: updates)(_ ++ Statement.getUpdatedVars(_))
    val transient = (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
    updated -- transient
  }
  
  //TODO can we have a method to eliminate the transient vars ?
  //as a special case of quantifier elimination ?
  //transient vars are used to preserve some difference between primed and unprimed


}

object Transition {

  //try to remove intermediate state (substitution / constrains propagation)
  def compact(trs: Seq[Transition]): Seq[Transition] = {
    for (i <- 0 until (trs.length -1) ) {
      assert(trs(i).targetPC == trs(i+1).sourcePC)
    }
    //substitution are easy and can be used for affectation
    //for equalities -> projection using an LP solver ?! 
    sys.error("TODO")
  }

}
