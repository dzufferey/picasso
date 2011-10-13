package picasso.frontend

import picasso.model.dbp._
import picasso.math._
import picasso.utils._
import picasso.analysis._

object DBPGraphs {

  /* The basic idea is: a series of transition where
   * a transition is pre graph, a post graph, a forward mapping and a backward mapping.
   * -a node is has an id and a label.
   * -an edge is from an id to an id with a label.
   * -a mapping is a list of id pairs.
   */

  type NodeId = String
  type NodeLabel = Option[String]
  class Node(n1: NodeId, n2: NodeLabel) extends Tuple2[NodeId, NodeLabel](n1, n2) {
    override def toString = n2 getOrElse "_"
  }

  trait DBCGraph extends DBCT {
    type State = Node
    type EL = String
  }
  
  implicit val ordering = new WellPartialOrdering[DBCGraph#State] {
    //a label that is not defined represents a wildcard.
    def tryCompare(x: DBCGraph#State, y: DBCGraph#State): Option[Int] = {
      val labelX = x._2
      val labelY = y._2
      if (labelX == labelY) Some(0)
      else if (!labelX.isDefined) Some(-1)
      else if (!labelY.isDefined) Some(1)
      else None
    }
    def lteq(x: DBCGraph#State, y: DBCGraph#State): Boolean = tryCompare(x, y).map(_ < 1).getOrElse(false)
  }

  def computeCoverKM(init: DepthBoundedConf[DBCGraph], transitions: List[DepthBoundedTransition[DBCGraph]]): DownwardClosedSet[DepthBoundedConf[DBCGraph]] = {
    val process = new DepthBoundedProcess[DBCGraph](transitions) with KarkMillerTree
    process.computeCover(init)
  }
  
  def computeCoverFW(init: DepthBoundedConf[DBCGraph], transitions: List[DepthBoundedTransition[DBCGraph]]): DownwardClosedSet[DepthBoundedConf[DBCGraph]] = {
    val process = new DepthBoundedProcess[DBCGraph](transitions) with ForwardWithWidening
    process.computeCover(init)
  }
  
  def computeCoverSF(init: DepthBoundedConf[DBCGraph], transitions: List[DepthBoundedTransition[DBCGraph]]): DownwardClosedSet[DepthBoundedConf[DBCGraph]] = {
    val process = new DepthBoundedProcess[DBCGraph](transitions) with SimpleForward
    process.computeCover(init)
  }

}
