package picasso.model.integer
  
import scala.collection.GenSeq

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
    new Program(initPC, trs2)
  }

  /** Return a map from PC location to the set of variables that may be non-zero at that location. */
  def nonZeroVariable: Map[String, Set[Variable]] = {
    //TODO similar to liveVariables

    sys.error("TODO")
  }
  /*
  lazy val liveVariables: Map[PC, Set[ID]] = {
    val read = readMap
    val written = writeMap
    assert(written.keySet == read.keySet)
    read.map{ case (k,v) => (k, v intersect written(k))}
  }

  //defaultValue: at the initState, the argument are written!
  lazy val writeMap: Map[PC, Set[ID]] = {
    def default(s: PC) = if (s == cfa.initState) params.toSet
                         else Set.empty[ID]
    cfa.aiFixpoint( ((written: Set[ID], p: Process) => written ++ p.writtenIDs),
                    ((a: Set[ID], b: Set[ID]) => a ++ b),
                    ((a: Set[ID], b: Set[ID]) => b subsetOf a),
                    default)
  }

  lazy val readMap: Map[PC, Set[ID]] = 
    cfa.aiFixpointBackward( ((read: Set[ID], p: Process) => read -- p.writtenIDs ++ p.readIDs),
                            ((a: Set[ID], b: Set[ID]) => a ++ b),
                            ((a: Set[ID], b: Set[ID]) => b subsetOf a),
                            (_ => Set.empty[ID]) )
  */

}
