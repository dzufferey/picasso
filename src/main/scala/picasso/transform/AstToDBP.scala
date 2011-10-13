package picasso.transform

import picasso.ast._
import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.Variable
import picasso.graph._

//TODO from AgentDefinition (a set of them) to a set of transition for DBP
//TODO from an initial state to a graph

//generic set of definition to help create DBP
trait DefDBP {

  type PC
  
  //on the state: an unique string ID
  trait DBC extends DBCT {
    type State = DBCS[PC]
    type EL = Variable
  }
   
  type DBCN = Thread[DBC#State]
  type DBCC = DepthBoundedConf[DBC]
  type DBT = DepthBoundedTransition[DBC]
  type DBP = DepthBoundedProcess[DBC]
  type PartialDBT = (String, DBCC, DBCC, Map[DBC#V,DBC#V], Map[DBC#V,DBC#V], Option[DBCC])
  
  implicit val ordering = new WellPartialOrdering[DBC#State] {
    def tryCompare(x: DBC#State, y: DBC#State): Option[Int] = {
      if (x == y) Some(0)
      else if (x.isWildcard) Some(-1)
      else if (y.isWildcard) Some(1)
      else if (x.states subsetOf y.states) Some(1)
      else if (y.states subsetOf x.states) Some(-1)
      else None
    }
    def lteq(x: DBC#State, y: DBC#State): Boolean = tryCompare(x, y).map(_ < 1).getOrElse(false)
  }

  val confOrdering = new WellPartialOrdering[DBCC] {
    def tryCompare(x: DBCC, y: DBCC): Option[Int] = {
      if (x == y) Some(0)
      else {
        val mxy = (x morphism y).isDefined
        val myx = (y morphism x).isDefined
        if (mxy && myx) Some(0) else
        if (mxy) Some(-1) else
        if (myx) Some(1) else
        None
      }
    }
    def lteq(x: DBCC, y: DBCC): Boolean = (x morphism y).isDefined
  }

  val emptyConf = DepthBoundedConf.empty[DBC]
  
  /** create a DBCC from edges */
  def makeConf(trvs: Traversable[(DBC#V, DBC#EL, DBC#V)]): DBCC = {
    DepthBoundedConf[DBC](Labeled.listToMap(trvs))
  }
  
  /** create a DBT from the individual component and do some sanity checks.
   *  TODO generate all the possible aliasing of wildcard nodes in the graphs.
   *  TODO variable type might help to exclude aliasing ...
   */
  def makeTrans(id: String, g1: DBCC, g2: DBCC, m1: Map[DBC#V,DBC#V], m2: Map[DBC#V,DBC#V], forbidden: Option[DBCC]): DBT = {
    //check that the mappings have the appropriate domains
    val m1Domain = g1.vertices //also m2 coDomain
    val m2Domain = g2.vertices //also m1 coDomain
    val m1p = m1.filterKeys(m1Domain(_))
    val m2p = m2.filterKeys(m2Domain(_))
    val g2WC = g2.vertices filter (_.state.isWildcard)
    /*
    Console.println(id)
    Console.println("g1: " + g1.toString)
    Console.println("g2: " + g2.toString)
    Console.println("m1: " + m1.toString)
    Console.println("m2: " + m2.toString)
    Console.println("wilcards: " + g2WC)
    Console.println("m2p: " + m2p)
    */
    assert(m1p.values.size == m1p.values.toSet.size)
    assert(m1p.values.forall(m2Domain(_)))
    assert(m2p.values.size == m2p.values.toSet.size)
    assert(m2p.values.forall(m1Domain(_)))
    //check that all wildcards from m2 are mapped to a node in m1
    assert(g2WC forall (m2p contains _))
    DepthBoundedTransition[DBC](id, g1, g2, m1p, m2p, forbidden)(ordering)
  }

  def DBCN(s: PC): DBCN = Thread(DBCS[PC](s))
  def DBCN(s: DBC#State): DBCN = Thread(s)
  
  /* match anything */
  def unk = DBCN(DBCS.unk[PC])

}

/* TODO
 * translation of patterns
 * translation of expression: boolean, stringLit
 * translation of send, receive
 * translation of create, new-channel, assert, assume, havoc
 * translation of set operations
 */
class AstToDBP[PC]() {

  //TODO type for the returned DBP
  //this can be copy pasted from compilerPlugin/backend/AuxDefinitions.scala
  //now the issue is that putting everything as nested classes limits the scope of what is visible and what we can do.
  //or put this at the top level, but then ...
  //or wrap it using mixin

  //check that the processes on the edges are things that are easy to translate.
  //otherwise it might need to unrolling
  def easyToTransform(agt: AgentDefinition[PC]): Boolean = {
    sys.error("TODO")
  }

  //def makeTransitions(agts: Seq[AgentDefinition[PC]]): ... {
  //}

}
