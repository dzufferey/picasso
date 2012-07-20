package picasso.analysis

import picasso.utils._
import picasso.model.dbp._
import picasso.graph._
import picasso.model.integer._
import picasso.math._
import scala.collection.parallel.{ParIterable, ParSeq}
import scala.text.Document
import scala.text.Document._

object TransitionsGraphFromCover {

  sealed abstract class TGEdges[P <: DBCT]
  case class Transition[P <: DBCT](witness: TransitionWitness[P]) extends TGEdges[P]
  case class Covering[P <: DBCT](morph: Map[P#V, P#V]) extends TGEdges[P]

  trait TG[P <: DBCT] extends GT {
    type V = DepthBoundedConf[P]
    type EL = TGEdges[P]
    type VL = Unit
  }

  def apply[P <: DBCT](proc: DepthBoundedProcess[P], cover: DownwardClosedSet[DepthBoundedConf[P]]): EdgeLabeledDiGraph[TG[P]] = {

    def oneStepPostWithWitness(current: DepthBoundedConf[P]): ParIterable[TransitionWitness[P]] = {
      val possible = proc.transitions.filter(_ isDefinedAt current).par
      for( t <- possible;
           (w,_) <- t.applyWithWitness( current ) ) yield {
          w
      }
    }
 
    def makeEdges(states: ParIterable[DepthBoundedConf[P]]): ParIterable[(DepthBoundedConf[P], TGEdges[P], DepthBoundedConf[P])] = {
      val oneStep = for ( s1 <- states; w <- oneStepPostWithWitness(s1) ) yield w
      val res1 = oneStep.map( w => (w.from, Transition(w), w.to) )
      val res2 = for ( w <- oneStep;
                       s2 <- states if proc.ordering.lteq(w.to, s2);
                       cov <- w.to.morphisms(s2)(proc.stateOrdering) ) yield {
        (w.to, Covering[P](cov), s2)
      }
      res1 ++ res2
    }
  
    val edges = makeEdges(cover.basis).seq
    EdgeLabeledDiGraph[TG[P]](edges)
  }

  def toGraphviz[P <: DBCT](graph: EdgeLabeledDiGraph[TG[P]]): Document = {

    val namer = new Namer
    val confToMap = scala.collection.mutable.HashMap[DepthBoundedConf[P], (String, Map[P#V, String])]()

    def printCluster(conf: DepthBoundedConf[P]/*, title: String*/): Document = {
      if (confToMap contains conf) {
        empty
      } else {
        val name = Namer("conf_")
        val (doc, map) = conf.toGraphvizFull("cluster_"+name, "subgraph", "label = "+ Misc.quote(name)+";", name + "_")
        confToMap += (conf -> ("cluster_"+name, map))
        doc
      }
    }

    def transition(witness: TransitionWitness[P]): Document = {
      val (n1, m1) = confToMap(witness.from)
      var curConf = witness.from
      var curName = n1
      var curMap = m1

      var docAcc: Document = empty

      def edgesTo(conf: DepthBoundedConf[P], morph: Iterable[(P#V, P#V)], title: String) {
        val graphDoc = printCluster(conf)
        val (gName, gMap) = confToMap(conf)
        val edges = for ( (a,b) <- morph.iterator ) yield text( curMap(a) + " -> " + gMap(b) + " [color=\"#0000aa\"];")
        val clusterToCluster: Document = text(Misc.quoteIfFancy(curName) + " -> " + Misc.quoteIfFancy(gName) + " [label=\""+title+"\"];")
        val all = (clusterToCluster /: edges)(_ :/: _)
        docAcc = graphDoc :/: all :/: docAcc
        curName = gName
        curConf = conf
        curMap = gMap
      }

      if (witness.unfolded != curConf) {
        val unfoldingRev = witness.unfolding.map{ case (a,b) => (b,a) }
        edgesTo(witness.unfolded, unfoldingRev, "unfolding")
      }

      if (witness.inhibited != curConf) {
        edgesTo(witness.inhibited, witness.inhibitedFlattening, "inhibiting")
      }

      edgesTo(witness.unfoldedAfterPost, witness.post, "post")

      if (witness.to != curConf) {
        val (n2, m2) = confToMap(witness.to)
        val edges = for ( (a,b) <- witness.folding.iterator ) yield text( curMap(a) + " -> " + m2(b) + " [color=\"#0000aa\"];")
        val clusterToCluster: Document = text(Misc.quoteIfFancy(curName) + " -> " + Misc.quoteIfFancy(n2) + " [label=\"folding\"];")
        val all = (clusterToCluster /: edges)(_ :/: _)
        docAcc = all :/: docAcc
      }

      docAcc
    }

    def cover(from: DepthBoundedConf[P], morph: Map[P#V, P#V], to: DepthBoundedConf[P]): Document = {
      val (n1, m1) = confToMap(from)
      val (n2, m2) = confToMap(to)
      val edges = for ( (a,b) <- morph.iterator ) yield text( m1(a) + " -> " + m2(b) + " [color=\"#0000aa\"];")
      (text(Misc.quoteIfFancy(n1) + " -> " + Misc.quoteIfFancy(n2) + " [label=\"covering\"];") /: edges)(_ :/: _)
    }

    //first part print all the conf in the graph (edges might add more confs, but their are not visible from outside)
    val confs = graph.vertices.map( printCluster(_) ).reduceLeft(_ :/: _)
    //2nd the edges:
    val trs = graph.edges.map{
      case (a, Transition(w), b) => transition(w)
      case (a, Covering(c), b) => cover(a, c, b)
    }.reduceLeft(_ :/: _)
    
    "digraph TG {" :: nest(4, confs :/: trs) :/: text("}")
  }

  /* TODO language extraction from the transition graph (should go innto its own file)
   * assume transition name / comment are of the from  "methodName(thisType)[: newObj] [, comment]"
   * methods that do not have this shape are transient methods (from wich the result should be integrated in the first correctly named predecessor).
   *
   * 1st step: identifies the equivalence classes (object node with the predicates)
   * 2nd step: go along the edges (and morphing) while tracking the equivalence classes of this and the other objects
   * 3rd step: structure the output ...
   */

}

