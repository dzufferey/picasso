package picasso.model.dbp

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.math._
import picasso.math.WellPartialOrdering._
import picasso.graph._

/* Keeping track of the morphisms to generate counter programs later. */

class TransitionWitness[P <: DBCT]( implicit wpo: WellPartialOrdering[P#State])
{

  type Conf = DepthBoundedConf[P]
  type Morphism = Map[P#V, P#V]

  var transition: DepthBoundedTransition[P] = null

  var from: Conf = null

  var to: Conf = null

  /** from transition.lhs to 'from' */
  //var firstMorhism: Morphism = null

  /** unfolding maps the unfolded nodes to their origin */
  var unfolding: Morphism = null
  /** 'from' after unfolding */
  var unfolded: DepthBoundedConf[P] = null
  /** firstMorhism after unfolding */
  //var unfoldedMorphism: Morphism = null

  //can be recomputed afterward
  /** nodes removed due to the inhibitor */
  var inhibitedNodes: Set[P#V] = Set[P#V]()
  var inhibitedFlattening: Morphism = null
  var inhibited: DepthBoundedConf[P] = null

  /** what happened during the post.
   *  For the moment this contains only the frame, since it is
   *  the only part that matter to update the counters
   */
  var post: Morphism = null

  /** conf after the removal of inhibited nodes and applying the transition */
  var unfoldedAfterPost: Conf = null

  /** how the configuration was folded */
  var folding: Morphism = null

  override def toString = {
    "TransitionWitness\n" +
    "transition: " + transition +
    "\nfrom: " + from +
    "\nunfolding: " + unfolding.mkString("\n", "\n", "\n") +
    "\nunfolded: " + unfolded +
    "\ninhibited nodes: " + inhibitedNodes.mkString(", ") +
    "\ninhibited flattening: " + inhibitedFlattening.mkString("\n", "\n", "\n") +
    "\ninhibited: " + inhibited +
    "\npost: " + post.mkString("\n", "\n", "\n") +
    "\npost unfolded: " + unfoldedAfterPost +
    "\nfolding: " + folding.mkString("\n", "\n", "\n") +
    "\nto: " + to
  }

  /** Complete the morphisms that are partial (no frame, only frame, ...). */
  def complete {
    // unfolding (no frame)
    unfolding = addFrame(unfolded, unfolding, from)
    // inhibitedFlattening (should already be complete)
    // post (only the frame + wildcard nodes)
    post = completePost(inhibited, post, unfoldedAfterPost)
    // folding (no frame)
    folding = addFrame(unfoldedAfterPost, folding, to)
  }

  protected def addFrame(src: DepthBoundedConf[P], map: Morphism, trg: DepthBoundedConf[P]): Morphism = {
    val frame = src.vertices -- map.keys
    Logger.assert(
      frame.forall(trg contains _),
      "DBP",
      "addFrame: node disappearing\n" + src + "\nframe: " + frame.mkString(", ") + "\n" + trg
    )
    (map /: frame)( (acc, f) => acc + (f -> f) )
  }

  protected def completePost(src: DepthBoundedConf[P], map: Morphism, trg: DepthBoundedConf[P]): Morphism = {
    val notFrameSrc = src.vertices -- map.keys
    val notFrameTrg = trg.vertices -- map.values
    //TODO map from notFrameSrc to transition.lhs
    //TODO map from notFrameTrg to transition.rhs
    //TODO the two mapping above might not be unique, but must agree.
    //TODO use hk (forward) complete the map, the hr part (backward) should already be there
    sys.error("TODO")
  }

  def reversedUnfolding: Map[P#V, Seq[P#V]] = {
    val frame = unfolded.vertices -- unfolding.keys
    assert(frame forall (from contains _) )
    val revMorph2 = unfolding ++ frame.map(x => (x,x))
    revMorph2.toSeq.map{ case (a,b) => (b,a) }.groupBy( _._1 ).mapValues( _ map (_._2) )
  }
  
  def isUnfoldingTrivial = {
    if (from == unfolded) {
      assert(unfolding.isEmpty)
      true
    } else {
      false
    }
  }

  def isInhibitingTrivial = {
    if (unfolded == inhibited) {
      assert(inhibitedNodes.isEmpty && inhibitedFlattening.isEmpty)
      true
    } else {
      false
    }
  }

  def isPostTrivial = {
    assert(inhibited != unfoldedAfterPost)
    false
  }

  def isFoldingTrivial = {
    if (unfoldedAfterPost == to) {
      assert(folding.isEmpty || folding.forall{ case (a,b) => a == b})
      true
    } else {
      false
    }
  }

  /** returns the nodes that are matched by the LHR. */
  def modifiedPre: Set[P#V] = sys.error("TODO")
  
  /** returns the nodes that are matched by the RHS. */
  def modifiedPost: Set[P#V] = sys.error("TODO")

  def modified: (Set[P#V], Set[P#V]) = (modifiedPre, modifiedPost)

}

class WideningWitness[P <: DBCT]( implicit wpo: WellPartialOrdering[P#State])
{
  type Conf = DepthBoundedConf[P]
  type Morphism = Map[P#V, P#V]

  var smaller: Conf = null
  var bigger: Conf = null
  var result: Conf = null

  //nodes -> node after replication
  var replicated: Morphism = null

  var unfoldedResult: Conf = null
  var folding: Morphism = null

}

class WideningWitnessSeq[P <: DBCT]
{
  
  type Conf = DepthBoundedConf[P]

  var from: Conf = null

  var to: Conf = null

  var sequence: List[WideningWitness[P]] = Nil

}
