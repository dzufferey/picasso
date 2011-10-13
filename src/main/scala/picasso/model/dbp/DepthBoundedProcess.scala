package picasso.model.dbp

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.math._
import picasso.math.WellPartialOrdering._
import picasso.graph._


class DepthBoundedProcess[P <: DBCT](trs: List[DepthBoundedTransition[P]])(implicit wpoConf: WellPartialOrdering[DepthBoundedConf[P]], wpoState: WellPartialOrdering[P#State]) extends WSTS with WADL {
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
  def transitions = trs

  def tryAcceleratePair(smaller: S, bigger: S): Option[S] = {
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
  }
}
