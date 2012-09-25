package picasso.model.integer
  
import scala.collection.GenSeq
import picasso.graph._
import picasso.utils._
import picasso.utils.tools.armc._

/** Integer Program.
 *  Integer program are use during the termination proof of DBP.
 *  Right now their purpose is just these termination check (not safety).
 */
class Program2(initPC: String, trs: GenSeq[Transition2]) extends picasso.math.TransitionSystem {
  
  type S = State
  
  //transition type
  type T = Transition2

  def initialPC = initPC

  def transitions: GenSeq[T] = trs

  lazy val pcs = (Set(initPC) /: trs)((acc, t) => acc + t.sourcePC + t.targetPC)

  lazy val variables: Set[Variable] = {
    trs.aggregate(Set[Variable]())(_ ++ _.variables, _ ++ _)
  }

  def printForARMC(writer: java.io.BufferedWriter) {
    sys.error("TODO")//ARMCPrinter(writer, this)
    writer.flush
  }
  
  def printForARMC: String = {
    val str = new java.io.StringWriter()
    val writer = new java.io.BufferedWriter(str)
    printForARMC(writer)
    writer.close
    str.toString
  }

  def simplifyForTermination = {
    sys.error("TODO")
  }

  /** Returns a map of which variable has a cst value at some location
   *  Type of the abstract domain: Map[Variable, Option[Int]]
   *  None means it is not cst
   *  Some(i) means it has value i
   *  not in the map means we don't know
   */
  def constantValueMap: Map[String,Map[Variable,Option[Int]]] = {
    sys.error("TODO")
  }

  /** propagate the constants values  */
  def propagateCst = {
    val map = constantValueMap
    Logger("integer.Program", LogDebug, "propagateCst: " + map)

    val trs2 = trs.par.map(t => {
      val preSubst = map(t.sourcePC).flatMap{ case (k, v) => v.map(i => (k, i)) }
      t.propagteInputConstants(preSubst)
    })
    new Program2(initPC, trs2)
    
  }

  def reduceNumberOfVariables = {
    sys.error("TODO")
  }
  
  def cfa: EdgeLabeledDiGraph[GT.ELGT{type V = String; type EL = Transition2}] = {
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = Transition2}]
    emp ++ (transitions.map(t => (t.sourcePC, t, t.targetPC)).seq)
  }
  
  protected def compactPath = {
    val trs2 = cfa.simplePaths.flatMap( path => {
      Transition2.compact(path.labels)
    })
    val p2 = new Program2(initPC, trs2)
    Logger("integer.Program", LogInfo, "compactPath: #transitions before = " + transitions.size + ", after = " + p2.transitions.size)
    p2
  }
  
  protected def duplicateTransitions: Program = {
    //is the same if for the same input it produce the same output (assuming determinism)
    //in the case of non-determinism, forall out1. exits out2. ... /\ out1 = out2 (and reverse)
    sys.error("TODO")
  }

}

object Program2 {

  def apply(p: Program): Program2 = {
    new Program2(p.initialPC, p.transitions.map(Transition2.apply))
  }

}
