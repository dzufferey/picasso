package picasso.model.dbp

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.math._
import picasso.math.WellPartialOrdering._
import picasso.graph._


class DepthBoundedTransition[P <: DBCT](id: String,
                                        lhs: DepthBoundedConf[P],
                                        rhs: DepthBoundedConf[P],
                                        hr: Map[P#V, P#V],
                                        hk: Map[P#V, P#V],
                                        inh: Option[DepthBoundedConf[P]] = None)(implicit wpo: WellPartialOrdering[P#State])
extends Transition[DepthBoundedConf[P]] 
{

  type Conf = DepthBoundedConf[P]
  type Morphism = Map[P#V, P#V]

  def apply(conf: Conf): Set[Conf] = {
    val homs = lhs.morphisms(conf)
    
    def removeInhibitors(conf: Conf, g: Morphism): Conf = {
      inh match {
        case Some(inhibitor) => {
          val gRestricted = g filter (p => inhibitor.vertices(p._1))
          val matches = inhibitor.morphisms(conf, gRestricted) 
          
          (conf /: matches) {
            (conf, m) =>
              val inhibited = m flatMap {p => if(g isDefinedAt p._1) Set[P#V]() else Set[P#V](p._2)}
              val coercedConf = conf -- inhibited 
              coercedConf
          }
        }
        case None => conf
      }
    }

    def post(g: Morphism): Conf = {
      val (conf0, g1) = conf.unfold(lhs, g)
      //print("conf1: " + conf1)
      //print("lhs: " + lhs.morph(g1))

      // remove all inhibiting subgraphs from conf0 (monotonicity abstraction)
      val conf1 = removeInhibitors(conf0, g1)
      
      // Compute nodes that the transition removes from conf1
      val hkRange = hk.values
      val removed = lhs.vertices.flatMap{v => if((hr isDefinedAt v) || (hkRange exists (_ == v))) Set[P#V]() else Set[P#V](g1(v))}
      //println ("removed: " + removed)

      // Frame is conf1 w/o the matched lhs and w/o dangling edges to removed nodes
      val frame = conf1 -- (lhs.morph(g1)) -- removed
      //print("frame: " + frame)      

      val (rhsClone, f) = rhs.clone

      // compute partial morphism conf1 -> rhs 
      val f_hr = hr.map[(P#V,P#V),Morphism]{p => (p._1, f(p._2))}
      val f_hr_g1 = g1.map[(P#V,P#V),Morphism]{p => (p._2, f_hr.getOrElse(p._1,p._2))}

      // compute partial morphism rhs -> conf1
      val hk_f = f.map[(P#V,P#V),Morphism]{p => (p._2, hk.getOrElse(p._1, p._2))}
      val g1_hk_f = hk_f mapValues (v => g1.getOrElse(v, v))
      //print("rhs: " + rhsClone)

      // add rhs to the frame and fold the result
      val postUnfolded = (frame morph f_hr_g1) ++ (rhsClone morph g1_hk_f)
      val post = postUnfolded.fold
      //print("post: " + post)
      post
    }

    homs.map(post).toSet
  }

  def isDefinedAt(conf: Conf): Boolean = true

  def toGraphviz(name: String, prefix: String = "digraph"): scala.text.Document = {
    import scala.text.Document._
    val inhib = inh.map(_.toGraphvizFull("cluster_"+name+"guard", "subgraph", "label = "+ Misc.quote("GUARD")+";", name+"guard")._1)
    val (pre, m1) = lhs.toGraphvizFull("cluster_"+name+"lhs", "subgraph", "label = "+ Misc.quote("LHS")+";", name+"lhs")
    val (post, m2) = rhs.toGraphvizFull("cluster_"+name+"rhs", "subgraph", "label = "+ Misc.quote("RHS")+";", name+"rhs")
    val title = if (prefix == "subgraph") empty :/: text("label = "+ Misc.quote(id)+";") else empty
    val name2 = if (prefix == "subgraph") "cluster_"+name else name
    val hrDoc = hr.filter{case (a,b) => (m1 contains a) && (m2 contains b)}.toList.map{case (a,b) => text( m1(a) + " -> " + m2(b) + "[color=\"#0000aa\"];")}
    val hkDoc = hk.filter{case (a,b) => (m2 contains a) && (m1 contains b)}.toList.map{case (a,b) => text( m1(b) + " -> " + m2(a) + "[dir=back color=\"#00aa00\"];")}
    //inh
    val mapEdges = hrDoc ::: hkDoc
    val body = ((title :/: (inhib getOrElse empty):/: pre :/: post) /: mapEdges)(_ :/: _)
    prefix :: " " :: name2 :: " {" :: nest(4, body) :/: text("}")
  }
}

object DepthBoundedTransition {
  def apply[P <: DBCT]( id: String,
                        lhs: DepthBoundedConf[P],
                        rhs: DepthBoundedConf[P],
                        h: Map[P#V, P#V],
                        hk: Map[P#V, P#V] = Map.empty[P#V, P#V],
                        inh: Option[DepthBoundedConf[P]] = None )(implicit wpo: WellPartialOrdering[P#State]): DepthBoundedTransition[P] = {
    new DepthBoundedTransition[P](id, lhs, rhs, h, hk, inh)(wpo)
  }
}
