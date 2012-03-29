package picasso.model.integer

//TODO should have a list of Statements 

class Transition(sourcePC: String,
                 targetPC: String,
                 guard: Condition,
                 updates: Seq[Statement]) extends picasso.math.Transition[State] {
  
  def apply(s: State): Set[State] = {
    sys.error("TODO: for the moment the analysis of interger program is shipped to other tool")
  }

  def isDefinedAt(s: State): Boolean = {
    sourcePC == s.pc
  }

}
