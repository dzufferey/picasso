package picasso.frontend.compilerPlugin.backend

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.frontend.compilerPlugin._
import picasso.ast.{Ident => PIdent, Process => PProcess, _}
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, Wildcard => HWildcard, Binding => HBinding, _}
import picasso.graph._
import picasso.model._
import picasso.math._
import scala.tools.nsc._

trait AuxDefinitions {
  self: AnalysisUniverse =>

  /////////////////////////
  // Definitions for DBP //
  /////////////////////////

  //introduce a more complex kind of nodes (more flexible than just PC) to accomodate more variantes of matching.
  //by convention when state is empty, this is a wildcard.
  class DBCS[A](val states: Set[A]) extends Equals {

    def isSingle = states.size == 1
    def isWildcard = states.size == 0

    def +(other: DBCS[A]) = new DBCS[A](states ++ other.states)

    override def canEqual(x: Any): Boolean = x match {
      case x: DBCS[_] => true //TODO bad: not possible to check the inner type due to erasure.
      case _ => false
    }

    override def equals(that: Any): Boolean = that match {
	  case that: DBCS[_] =>
	    (this eq that) ||
	    ((that canEqual this) &&
	     (try this.states == that.asInstanceOf[DBCS[A]].states
	      catch { case ex: ClassCastException => false }))
	  case _ =>
	    false
	}

    override def toString = if (isWildcard) "_" else states.mkString("","|","")

  }

  object DBCS {
    def apply[A](trs: Traversable[A]) = {
      assert(!trs.isEmpty)
      new DBCS[A](trs.toSet)
    }
    def apply[A](s: A) = new DBCS(Set[A](s))
    def unk[A]: DBCS[A] = new DBCS[A](Set.empty[A])
  }
  
  //on the edges: the name of the things pointing to
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
  
  def nodeForLiteral[T](l : Literal[T]) = DBCN(l.toString)


  /** a generic name in the pi-calculus sense. */
  def fresh = DBCN("name")
  /* match anything */
  def unk = DBCN(DBCS.unk[PC])

  def errorState = DBCN("error")
  
  def matchTrueAny = DBCN(DBCS[PC](Set("true","Any")))
  def matchFalseAny = DBCN(DBCS[PC](Set("false","Any")))
  def matchTrueFalseAny = DBCN(DBCS[PC](Set("true","false","Any")))

  ///////////////////////////////////////////////////
  // Additional elements introduced by translation //
  ///////////////////////////////////////////////////
  
  val thisVar = Variable("this") setType Channel() //TODO this should have the type of the class it is associated with
  val thisChannel = ID(thisVar)

  /** Message destination */
  val msgDest = Variable("to") setType Channel()
  
  /** Wrap content + return address into a 'Message' */
  def addReturnAddress(msg: Expression, returnAddress: Expression = thisChannel) = Application("Message", List(returnAddress, msg))
  /** Unwrap a message and match the sender */
  def unpackMessageWithSender(p: Pattern): Pattern = Case("Message", List(PIdent(senderChannel), p))
  /** Unwrap a message without matching the sender */
  def unpackMessageWoSender(p: Pattern): Pattern = Case("Message", List(Wildcard, p))
  
  /** receive, react */
  lazy val senderChannel = ID(Variable("sender") setType typeOfType(senderType))
  /** !? */
  lazy val sendSync = ID(Variable("sendSync") setType typeOfType(senderType))

  //about the return from a fct call
  val retVar = Variable("return") setType Channel() //TODO a better way to type ?
  val retID = ID(retVar)
  val returnIdent = PIdent(retID)

  //about collections
  def defaultCollectionNode = DBCN("collection")
  def collectionMember(collection: Variable) = collection.tpe match {
    case Collection(_, element) => Variable("member") setType element
    case other => Logger.logAndThrow("Plugin", LogError, "collection do not have collection type" + other)
  }

  //////////////////////
  // Needed in PiCode //
  //////////////////////

  /** program counter (states of the automata) */
  type PC = String

  /** Intermediate Automaton: used to get rid of the 'Global' suffs */
  type IA = GT {
    type V = PC
    type VL = Unit
    type EL = PProcess
  }
}
