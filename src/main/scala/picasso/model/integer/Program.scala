package picasso.model.integer
  
import scala.collection.GenSeq
import picasso.graph._

  //what is an ARMC/T2/integer program:
  // program location
  // variables
  // transition (var updates for T2, set of constraints for ARMC)
  // a start location
  // cutpoints (for ARMC)
  //the simplest thing might be to have somthing between T2 and ARMC:
  // get updates like T2, but with an all at the same time semantics like ARMC.

/** Integer Program.
 *  Integer program are use during the termination proof of DBP.
 *  Right now their purpose is just these termination check (not safety).
 */
class Program(initPC: String, trs: GenSeq[Transition]) extends picasso.math.TransitionSystem {
  
  type S = State
  
  //transition type
  type T = Transition

  def initialPC = initPC

  def transitions: GenSeq[T] = trs

  def variables: Set[Variable] = {
    trs.aggregate(Set[Variable]())(_ ++ _.variables, _ ++ _)
  }

  def printForARMC = {
    val str = new java.io.StringWriter()
    val writer = new java.io.BufferedWriter(str)
    ARMCPrinter(writer, this)
    writer.close
    str.toString
  }
  
  def printForQARMC = {
    val str = new java.io.StringWriter()
    val writer = new java.io.BufferedWriter(str)
    QARMCPrinter(writer, this)
    writer.close
    str.toString
  }
  
  def printForT2 = {
    sys.error("TODO")
  }

  /** try to simplify the program while preserving (non)termination. */
  def simplifyForTermination = {
    val trs2 = transitions.map(_.leaner)
    //TODO compact the transitions
    //TODO merge the variables (liveness + transfer analysis)
    //TODO transition in sequence that operates on disjoint set of variable might be merged (if the control flow is linear)
    //if two variables are not live at the same moment, we can merge them!
    new Program(initPC, trs2)
  }

  /** Return a map from PC location to the set of variables that may be non-zero at that location. */
  protected def nonZeroVariable: Map[String, Set[Variable]] = {
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = Transition}]
    val cfa = emp ++ (transitions.map(t => (t.sourcePC, t, t.targetPC)).seq)
    val allVars = variables
    def default(s: String) = if (s == initPC) allVars else Set[Variable]()
    cfa.aiFixpoint( ((nonZeros: Set[Variable], t: Transition) => nonZeros -- t.assignedToZero ++ t.assignedToNonZero),
                    ((a: Set[Variable], b: Set[Variable]) => a ++ b),
                    ((a: Set[Variable], b: Set[Variable]) => b subsetOf a),
                    default)
  }

  /** Return a list of groups of variables that may be merged safely.
   *  A safe merge means that the variables in a group are never non-zero at the same time.
   */
  protected def computeVariableMerge: Seq[Set[Variable]] = {
    val nonZeroMap = nonZeroVariable - initPC
    //we can build a conflict graph where variables are in conflict iff they are live at the same time.
    val conflictsTmp = (DiGraph.empty[GT.ULGT{type V = Variable}] /: nonZeroMap)( (acc, kv) => {
      val group = kv._2
      val edges = for (x <- group; y <- group if x != y) yield (x, (), y)
      acc ++ edges
    })
    //Then we need to find a minimal coloring of the graph
    //Since the problem is hard it makes sense to use a greedy algorithm with heuristics rather than finding an optimal coloring.
    //TODO look at http://shah.freeshell.org/graphcoloring/ or http://code.google.com/p/graphcol/ for some good heuristic
    //The idea of the greedy algorithm is to associate the first available color to a node.
    //To add the heuristics, we should rank the available colors according to some distance.
    //In this case two nodes are close if they share a long prefix.
    //another idea is to look at which variable flow into which one.
    sys.error("TODO")
  }

}
