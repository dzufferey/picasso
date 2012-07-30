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
    // post
    //The post should already be complete. TODO how to make sure this is the case ?
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

  def reversedUnfolding: Map[P#V, Seq[P#V]] = {
    val frame = unfolded.vertices -- unfolding.keys
    assert(frame forall (from contains _) )
    val revMorph2 = unfolding ++ frame.map(x => (x,x))
    revMorph2.toSeq.map{ case (a,b) => (b,a) }.groupBy( _._1 ).mapValues( _ map (_._2) )
  }
  
  def isUnfoldingTrivial = {
    if (from == unfolded) {
      assert(unfolding.forall{ case (a,b) => a == b})
      true
    } else {
      false
    }
  }

  def isInhibitingTrivial = {
    if (unfolded == inhibited) {
      assert(inhibitedNodes.isEmpty && inhibitedFlattening.forall{ case (a,b) => a == b})
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
      assert(folding.forall{ case (a,b) => a == b})
      true
    } else {
      false
    }
  }

  protected def postChanging: Morphism = post.filter{ case (a,b) => a != b } //TODO not sure about the wildcards

  /** returns the nodes that are matched by the LHR. */
  def modifiedPre: Set[P#V] = {
    //println("unfolded = " + unfolded)
    //println("post = " + post.mkString(", "))
    //println("postChanging = " + postChanging.mkString(", "))
    val before = postChanging.keySet
    val revInh = inhibitedFlattening.map[(P#V,P#V), Morphism]{ case (a,b) => (b,a) }
    val beforeInhibit = before.map(n => revInh.getOrElse(n,n) )
    beforeInhibit.map(n => unfolding.getOrElse(n,n))
  }
  
  /** returns the nodes that are matched by the RHS. */
  def modifiedPost: Set[P#V] = {
    val after = postChanging.values.toSet
    after.map(n => folding.getOrElse(n,n))
  }

  def modified: (Set[P#V], Set[P#V]) = (modifiedPre, modifiedPost)

  protected def checkMorph( name: String,
                            a: DepthBoundedConf[P],
                            m: Morphism,
                            b: DepthBoundedConf[P]) {
    Logger.assert(
      m.keySet subsetOf a.vertices,
      "DBP", name + ".keys is not correct")
    Logger.assert(
      m.values forall b.vertices,
      "DBP", name + ".values is not correct")
  }

  def checkMorphisms {
    //  from: Conf
    //  unfolding: Morphism
    checkMorph("unfolding", unfolded, unfolding, from)
    //  reversedUnfolding: Map[P#V, Seq[P#V]]
    Logger.assert(
      reversedUnfolding.keySet subsetOf from.vertices,
      "DBP", "reversedUnfolding.keys is not correct")
    Logger.assert(
      reversedUnfolding.values.forall(_ forall unfolded.vertices),
      "DBP", "reversedUnfolding.values is not correct")
    //  unfolded: DepthBoundedConf[P]
    //  inhibitedNodes: Set[P#V]
    Logger.assert(
      inhibitedNodes subsetOf unfolded.vertices,
      "DBP", "inhibitedNodes is not correct")
    //  inhibitedFlattening: Morphism
    checkMorph("inhibitedFlattening", unfolded, inhibitedFlattening, inhibited)
    //  inhibited: DepthBoundedConf[P]
    //  post: Morphism
    checkMorph("post", inhibited, post, unfoldedAfterPost)
    //  unfoldedAfterPost: Conf
    //  folding: Morphism
    checkMorph("folding", unfoldedAfterPost, folding, to)
    //  to: Conf
  }

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
