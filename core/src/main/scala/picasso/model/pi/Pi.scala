package picasso.model.pi

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.math._
import picasso.math.WellPartialOrdering._

/*
object PiProgram {
    
  def isConfiguration(p: PiProcess): Boolean  = p match {
    case Composition(processes) => processes.forall(isConfiguration)
    case Restriction(_, process) => isConfiguration(process)
    case Repetition(process) => isConfiguration(process)
    case PiZero => true
    case PiProcessID(_,_) => true
    case _ => false
  }
  
  import scala.collection.immutable.TreeMap
  def instanciateDefinition(pid: String, args: List[String], definition: Map[String,(List[String], PiProcess)]): PiProcess = definition get pid match {
    case Some((params, p)) => {
      val map = (TreeMap.empty[String,String] /: (params zip args))(_ + _)
      p alpha map
    }
    case None => error("PiProgram.instanciateDefinition: " + pid +" not found")
  }

  //TODO define normal form where equations have a prefix/choice/replication first
  //TODO normal form for the configuration: restriction at top level, or just below replication, then composition of PIDs

  private def removeRestrictions(configuration: PiProcess): PiProcess = configuration match {
    case Restriction(_, process) => removeRestrictions(process)
    case process => process
  }

  def findProcessID(configuration: PiProcess, id: String): List[PiProcessID] = {
    val stripped = removeRestrictions(configuration)
    configuration match {
      case Composition(processes) => {
        ((Nil: List[PiProcessID]) /: processes)( (acc, p) => p match {
          case pid @ PiProcessID(_,_) => pid::acc
          case Restriction(_,_) =>
            Logger("DepthBoundedProcess", LogWarning, "PiProgram.findProcessID does not yet handle restriction")
            acc
          case _ => error("PiProgram.findProcessID: configuration not in normal form (ProcessID/Restriction)")
        })
      }
      case _ => error("PiProgram.findProcessID: configuration not in normal form Composition")
    }
  }
    
}

object PiProcessWPO extends WellPartialOrdering[PiProcess] {

  def tryCompare(p1: PiProcess, p2: PiProcess): Option[Int] = {
    //TODO transform progams into some kind of graph and call somegraph isomosphism
    //put graph as lazy val into the process ?
    error("TODO")
  }

  def lteq(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(0) | Some(-1) => true; case _ => false }
  
  override def lt(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(-1) => true; case _ => false }
  
  override def equiv(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(0) => true; case _ => false }
  
  override def gteq(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(0) | Some(1) => true; case _ => false }
  
  override def gt(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(1) => true; case _ => false }

}

/** a transition happening on (co-)name observable*/
class PiTransition(observable: String, definition: Map[String,(List[String], PiProcess)]) extends Transition[PiProcess] {

  private def findMatchingParams(p: PiProcess, template: (String,(List[String], PiProcess))): List[(String, List[String], PiProcess)] = {
    val matchingPID = PiProgram.findProcessID(p, template._1)
    matchingPID map { case PiProcessID(id, args) => 
      val zipped = template._2._1 zip args
      val substitution = (Map.empty[String,String] /: zipped)(_ + _)
      (id, args, template._2._2 alpha substitution)
    }
  }

  private def matchAndFilter(s: PiProcess, defs: Map[String,(List[String], PiProcess)]): List[(String,List[String], PiProcess)] = {
    defs.toList flatMap ( mapping => {
      val instanciated = findMatchingParams(s, mapping)
      instanciated filter (_._3 isObservablePrefix observable)
    })
  }


  private val receiving: Map[String,(List[String], PiProcess)] = definition filter ( (p: (String,(List[String], PiProcess))) => isInputPrefix(p._2._2))
  /** Returns the process ID that are receiving on observable */
  def name(s: PiProcess) = matchAndFilter(s, receiving)
  
  private val sending: Map[String,(List[String], PiProcess)] = definition filter ( (p: (String,(List[String], PiProcess))) => isOutputPrefix(p._2._2))
  /** Returns the process ID that are sending on observable */
  def coname(s: PiProcess) = matchAndFilter(s, sending)

  def apply(state: PiProcess): Set[PiProcess] = {
    error("TODO")
  }

  def isDefinedAt(state: PiProcess): Boolean = !(name(state).isEmpty || coname(state).isEmpty)
}
*/
//TODO extends WSTS with WADL
//class PiProgram(definition: Map[String,(List[String], PiProcess)], configuration: PiProcess) extends WSTS with PredBasis {
//
//  type S = PiProcess
//  implicit val ordering: WellPartialOrdering[S] = PiSubGraph
//  tpye T = ...
//  val transitions = Nil //TODO to have an easily computable #of transitions: a transition is givent by a pair of InputPrefix/OutputPrefix
//  def predBasis(s: UpwardClosedSet[S]): UpwardClosedSet[S] = error("TODO")
//  //TODO
//
//}
