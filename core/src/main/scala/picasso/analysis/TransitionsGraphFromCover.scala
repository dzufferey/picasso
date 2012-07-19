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
      val res1 = for ( s1 <- states;
                       w <- oneStepPostWithWitness(s1) ) yield {
        (s1, Transition(w), w.to)
      }
      val res2 = for ( s1 <- states;
                       w <- oneStepPostWithWitness(s1);
                       s2 <- states if proc.ordering.lteq(w.to, s2);
                       cov <- s1.morphisms(s2)(proc.stateOrdering) ) yield {
        (w.to, Covering[P](cov), s2)
      }
      res1 ++ res2
    }
  
    val edges = makeEdges(cover.basis).seq
    EdgeLabeledDiGraph[TG[P]](edges)
  }

  def toGraphiz[P <: DBCT](graph: EdgeLabeledDiGraph[TG[P]]): Document = {

    val namer = new Namer
    val confToMap = scala.collection.mutable.HashMap[DepthBoundedConf[P], (String, Map[P#V, String])]()

    def printCluster(conf: DepthBoundedConf[P]/*, title: String*/): Document = {
      val name = Namer("conf_")
      val (doc, map) = conf.toGraphvizFull("cluster_"+name, "subgraph", "label = "+ Misc.quote(name)+";", name)
      confToMap += (conf -> ("cluster_"+name, map))
      doc
    }

    def transition(witness: TransitionWitness[P]): Document = {
      val (n1, m1) = confToMap(witness.from)
      val (n2, m2) = confToMap(witness.to)
      //TODO print the intermediate graph and the edges
      sys.error("TODO")
    }

    def cover(from: DepthBoundedConf[P], morph: Map[P#V, P#V], to: DepthBoundedConf[P]): Document = {
      val (n1, m1) = confToMap(from)
      val (n2, m2) = confToMap(to)
      val edges = for ( (a,b) <- morph.toSeq ) yield text( m1(a) + " -> " + m2(b) + " [color=\"#0000aa\"];")
      (text(n1 + " -> " + n2 + " [label=\"covering\"];") /: edges)(_ :/: _)
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

}

