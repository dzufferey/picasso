package picasso.ast

import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.{Variable, Literal, Channel}
import picasso.graph._

trait DBC extends DBCT {
  //on the state: an unique string ID
  type State = DBCS[String]
  type EL = Variable
}

//generic set of definition to help create DBP
trait DefDBP {

  type PC = String

   
  //type DBCN = Thread[DBC#State] = DBC#V
  type DBCC = DepthBoundedConf[DBC]
  type DBT = DepthBoundedTransition[DBC]
  type DBP = DepthBoundedProcess[DBC]
  type PartialDBT = (String, DBCC, DBCC, Map[DBC#V,DBC#V], Map[DBC#V,DBC#V], Option[(DBCC, Map[DBC#V,DBC#V])])
  
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

  def DBCN(s: PC): DBC#V = Thread(DBCS[PC](s))
  def DBCN(s: DBC#State): DBC#V = Thread(s)
  
  /* match anything */
  def unk = DBCN(DBCS.unk[PC])
  def isUnk(s: DBC#V) = s.state.isWildcard

  /** Message destination */
  val msgDest = Variable("to") setType Channel()

  //Methods that needs to be implemented by classes extending this trait

  def DBCN[T](s: Literal[T]): DBC#V
  def DBCN_Any: DBC#V
  def DBCN_Name: DBC#V //a pi-calculus name
  def DBCN_Unit: DBC#V
  def DBCN_Case(uid: String): DBC#V //case class
  def DBCN_Error: DBC#V //assert fail or something like that


  /////////////////////////////////////////////////////////
  // Methods to help creating configuration, transitions //
  /////////////////////////////////////////////////////////

  
  /** create a DBCC from edges */
  def makeConf(trvs: Traversable[(DBC#V, DBC#EL, DBC#V)]): DBCC = {
    DepthBoundedConf[DBC](Labeled.listToMap(trvs): Map[DBC#V, Map[DBC#EL, Set[DBC#V]]])
  }
  
  /** create a DBT from the individual component and do some sanity checks.
   *  TODO generate all the possible aliasing of wildcard nodes in the graphs.
   *  TODO variable type might help to exclude aliasing ...
   *  TODO the mapping from g1 to forbidden
   */
  def makeTrans(id: String, g1: DBCC, g2: DBCC, m1: Map[DBC#V,DBC#V], m2: Map[DBC#V,DBC#V], forbidden: Option[(DBCC, Map[DBC#V,DBC#V])]): DBT = {
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
    
    val forbiddenp = for ( (inh, m3) <- forbidden ) yield {
      val m3p = m3.filterKeys(m1Domain(_))
      val m3pRange = m3p.values.toSet.size
      assert(m3p.values.size == m3pRange)
      assert(m3pRange <= inh.vertices.size)
      assert(m3p.forall {case (k, v) => g1.labelOf(k) == inh.labelOf(v) })
      (inh, m3p)
    }

    DepthBoundedTransition[DBC](id, g1, g2, m1p, m2p, forbiddenp )(ordering)
  }
  
  def makeTrans(partial: PartialDBT): DBT = {
    val (id, g1, g2, m1, m2, forbidden) = partial
    makeTrans(id, g1, g2, m1, m2, forbidden)
  }

  def checkTransition(tr: DBT): DBT = {
    makeTrans(tr.id, tr.lhs, tr.rhs, tr.hr, tr.hk, tr.inh)
  }

}

