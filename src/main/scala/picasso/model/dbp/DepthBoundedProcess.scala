package picasso.model.dbp

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, MultiSet}
import picasso.math._
import picasso.math.WellPartialOrdering._
import picasso.graph._
import scala.collection.{GenSeq, GenIterable, GenMap}


class DepthBoundedProcess[P <: DBCT](trs: GenSeq[DepthBoundedTransition[P]])(implicit wpoConf: WellPartialOrdering[DepthBoundedConf[P]], wpoState: WellPartialOrdering[P#State]) extends WSTS with WADL {
  type S = DepthBoundedConf[P]
  implicit val ordering : WellPartialOrdering[S] = wpoConf
  val stateOrdering = wpoState

  /** copy constructor */
  def this(dbp: DepthBoundedProcess[P]) = this(dbp.transitions)(dbp.ordering, dbp.stateOrdering)

  def toGraphviz(name: String): scala.text.Document = {
    import scala.text.Document._
    var x = 0
    val docOfTrs = trs map ( t => {
      x = x + 1
      t.toGraphviz("transition_"+x, "subgraph")
    })
    val oneDoc = docOfTrs.reduceRight(_ :/: _)
    "digraph" :: " " :: name :: " {" :: nest(4, empty :/: oneDoc) :/: text("}")
  }
  
  type T = DepthBoundedTransition[P]
  val trs2 = trs.par
  def transitions = trs2

  /** accelration/widening with witness:
   * returns:
   * - the result
   * - the set of replicated nodes
   * - the result before folding
   * - the mapping used for the folding
   */
  def tryAcceleratePairWithWitness(smaller: S, bigger: S): Option[(S, WideningWitness[P])] = {
    val ms = (smaller morphisms bigger).toSeq
    val seeds = ms.map(m => bigger.vertices -- m.values)
    val (widenedUnfolded, usedSeed) = ((bigger, Map[P#V,P#V]()) /: seeds)( (acc, seed) => {
      val (w,m) = bigger widenWithWitness seed
      if (ordering.gt(acc._1, w)) acc else (w, m)
    })
    val (widened, folding) = widenedUnfolded.foldWithWitness
    //println("Acceleration:")
    //print(smaller.toGraphviz("smaller"))
    //print(bigger.toGraphviz("bigger"))
    //print(widenend.toGraphviz("widenend"))
    if (usedSeed.isEmpty) None
    else {
       val witness = new WideningWitness
       witness.smaller = smaller
       witness.bigger = bigger
       witness.result = widened
       witness.replicated = usedSeed
       witness.unfoldedResult = widenedUnfolded
       witness.folding = folding
       Some((widened, witness))
    }
  }

  def tryAcceleratePair(smaller: S, bigger: S): Option[S] = {
    tryAcceleratePairWithWitness(smaller, bigger).map(_._1)
  }
  
  def wideningWithWitness(smaller: S, bigger: S): (S, WideningWitness[P]) = {
    val opt = tryAcceleratePairWithWitness(smaller, bigger)
    if (opt.isDefined) opt.get
    else Logger.logAndThrow("Limits", LogError, "widening not defined for " + smaller + " and " + bigger)
  }

  lazy val affinityMap: GenMap[(T,T), Int] = {
    val pairs = for (t1 <- transitions; t2 <- transitions) yield {
      //as produced: look at the nodes in t1.rhs that are not in t1.lhs (as a multiset)
      val same1 = t1.hr.filter{ case (a,b) => a.state == b.state }
      val produced = (t1.rhs -- same1.values -- t1.hk.keys).vertices
      val producedLabels = MultiSet[P#State](produced.toSeq.map(_.state): _*)
      //as consummed: look at the nodes in t2.lhs that are not in t2.rhs (as a multiset)
      val same2 = t2.hr.filter{ case (a,b) => a.state == b.state }
      val consummed = (t2.lhs -- t2.hk.values -- same2.keys).vertices
      val consummedLabels = MultiSet[P#State](consummed.toSeq.map(_.state): _*)
      //then return the cardinality of the intersection of the two multisets
      val aff = (producedLabels intersect consummedLabels).size
      //Console.println("affinity of " + t1 + " => " + t2 + " is " + aff)
      //Console.println("producedLabels = " + producedLabels)
      //Console.println("consummedLabels = " + consummedLabels)
      ((t1, t2), aff)
    }
    ////////////////////
    //TODO here is a good idea to partition 
    //val edges: Iterable[(T,T)] = pairs.filter(_._2 > 0).map(_._1).seq
    //val trsGraph = DiGraph[GT.ULGT{type V = T}](edges)
    //Console.println("|edges| = " + edges.size)
    //Console.println("|graph| = " + trsGraph.vertices.size)
    //val intGraph = trsGraph.morphFull[GT.ULGT{type V = Int}]((t => t.hashCode()), _ => (), _ => ())
    //Console.println("graph = " + intGraph.toGraphviz("IG"))
    //val sccs = intGraph.SCC
    //Console.println("|scc| = " + sccs.size)
    //Console.println("scc = \n" + sccs.mkString("","\n",""))
    ////////////////////
    pairs.toMap
  }
  def transitionsAffinity(t1: T, t2: T): Int = affinityMap(t1 -> t2)
}
