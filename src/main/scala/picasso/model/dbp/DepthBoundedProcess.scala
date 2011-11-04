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

  def tryAcceleratePair(smaller: S, bigger: S): Option[S] = {
    //go over all the morphisms ...
    val ms = (smaller morphisms bigger).toSeq
    val seeds = ms.map(m => bigger.vertices -- m.values)
    val widenend = (bigger /: seeds)( (acc, seed) => {
      val w = bigger widen seed
      if (ordering.lt(acc, w)) w else acc
    })
    if (ms.isEmpty) None
    else Some(widenend.fold)
    /*
    smaller morphism bigger match {
      case None => None
      case Some(m) => {
        val newThreads = bigger.vertices -- m.values
        
        val accBigger = bigger widen newThreads

        //println("Acceleration:")
        //print(smaller.toGraphviz("smaller"))
        //print(bigger.toGraphviz("bigger"))
        //print(accBigger.toGraphviz("accBigger"))
        
        Some((bigger widen newThreads).fold)

        /*
        val threadsInc = new scala.collection.mutable.HashMap[S#V,S#V]
        val mapping: PartialFunction[S#V,S#V] = 
          threadsInc orElse { case v =>
            if (!(newThreads contains v)) v else {
              val vInc = v++
              threadsInc += (v -> vInc)
              vInc
            }
          }

        val accBigger = bigger morph mapping

        if (threadsInc.values.forall (_.depth > 1)) Some(bigger) else Some(accBigger)
        */
      }
    }
    */
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
