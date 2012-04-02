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
  var inhibited: DepthBoundedConf[P] = null

  /** what happened during the post */
  var post: Morphism = null

  /** conf after the removal of inhibited nodes and applying the transition */
  var unfoldedAfterPost: Conf = null

  /** how the configuration was folded */
  var folding: Morphism = null

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