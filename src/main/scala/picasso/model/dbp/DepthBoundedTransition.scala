package picasso.model.dbp

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.math._
import picasso.math.WellPartialOrdering._
import picasso.graph._


class DepthBoundedTransition[P <: DBCT](val id: String,
                                        val lhs: DepthBoundedConf[P],
                                        val rhs: DepthBoundedConf[P],
                                        val hr: Map[P#V, P#V],
                                        val hk: Map[P#V, P#V],
                                        val inh: Option[(DepthBoundedConf[P], Map[P#V, P#V])] = None)
                                       (implicit wpo: WellPartialOrdering[P#State])
extends Transition[DepthBoundedConf[P]] 
{

  type Conf = DepthBoundedConf[P]
  type Morphism = Map[P#V, P#V]



  //TODO modify to generated TransitionWitness(es)
  def apply(conf: Conf): Set[Conf] = {
    val homs = lhs.morphisms(conf)
    
    //g: lhs -> conf
    //TODO this is not quite monotonic:
    // removing all the matches can lead to a situation where the transition cannot be applied,
    // even though removing some matches can lead to a situation where the transition can still be applied.
    // for the moment, we will assume the transition are 'nice'
    def removeInhibitors(conf: Conf, g: Morphism): Option[Conf] = {
      inh match {
        case Some((inhibitor, inhMap)) => {
          //get the mapping of the inhibitor starting form the inhMap
          //val gRestricted = g filter (p => inhibitor.vertices(p._1))
          val gRestricted = g filterKeys (inhMap contains _)
          val partialMorphism: Morphism = gRestricted.map{ case (k,v) => (inhMap(k), v) }.toMap
          val matches = inhibitor.morphisms(conf, partialMorphism) 

          val inhMapRange = inhMap.values.toSet
          val nodesToRemove = inhibitor.vertices.filter(v => !inhMapRange.contains(v))
          
          //for each of such match removes the part which is not in the range of inhMap
          val notInhibited = (conf /: matches) {
            (conf, m) =>
              val nodesToRemoveMapped = nodesToRemove.map(m(_))
              val coercedConf = conf -- nodesToRemoveMapped
              coercedConf
          }
          //make sure that the morphism g is still valid after removing the inhibitors
          if ( g.values.forall(v => notInhibited contains v) ) {
            Some( notInhibited )
          } else {
            None
          }
        }
        case None => Some(conf)
      }
    }

    def post(g: Morphism): Option[Conf] = {
      val (conf0, g1) = conf.unfold(lhs, g)
      //print("conf1: " + conf1)
      //print("lhs: " + lhs.morph(g1))

      // remove all inhibiting subgraphs from conf0 (monotonicity abstraction)
      for ( conf1 <- removeInhibitors(conf0, g1) ) yield {
      
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
    }

    homs.flatMap(post).toSet
  }

  //TODO this is not really what should happen:
  //need to check if the LHS match, then that the inhibitor does not.
  def isDefinedAt(conf: Conf): Boolean = true

  def toGraphviz(name: String, prefix: String = "digraph"): scala.text.Document = {
    import scala.text.Document._
    val (pre, m1) = lhs.toGraphvizFull("cluster_"+name+"lhs", "subgraph", "label = "+ Misc.quote("LHS")+";", name+"lhs")
    val (post, m2) = rhs.toGraphvizFull("cluster_"+name+"rhs", "subgraph", "label = "+ Misc.quote("RHS")+";", name+"rhs")
    val title = if (prefix == "subgraph") empty :/: text("label = "+ Misc.quote(id)+";") else empty
    val name2 = if (prefix == "subgraph") "cluster_"+name else name
    val hrDoc = hr.filter{case (a,b) => (m1 contains a) && (m2 contains b)}.toList.map{case (a,b) => text( m1(a) + " -> " + m2(b) + "[color=\"#0000aa\"];")}
    val hkDoc = hk.filter{case (a,b) => (m2 contains a) && (m1 contains b)}.toList.map{case (a,b) => text( m1(b) + " -> " + m2(a) + "[dir=back color=\"#00aa00\"];")}
    val (inhib, inhMap) = inh match {
      case Some((inGraph, inMap)) => 
        val (inhibDoc, m3) = inGraph.toGraphvizFull("cluster_"+name+"guard", "subgraph", "label = "+ Misc.quote("GUARD")+";", name+"guard")
        val inhMap = inMap.filter{case (a,b) => (m1 contains a) && (m3 contains b)}.toList.map{case (a,b) => text( m1(a) + " -> " + m3(b) + "[dir=back color=\"#aa0000\"];")}
        (inhibDoc, inhMap)
      case None => (empty, Nil)
    }
    //inh
    val mapEdges = hrDoc ::: hkDoc ::: inhMap
    val body = ((title :/: inhib :/: pre :/: post) /: mapEdges)(_ :/: _)
    prefix :: " " :: name2 :: " {" :: nest(4, body) :/: text("}")
  }

  override def toString = Misc.docToString(toGraphviz("DBT"))
}

object DepthBoundedTransition {
  def apply[P <: DBCT]( id: String,
                        lhs: DepthBoundedConf[P],
                        rhs: DepthBoundedConf[P],
                        h: Map[P#V, P#V],
                        hk: Map[P#V, P#V] = Map.empty[P#V, P#V],
                        inh: Option[(DepthBoundedConf[P], Map[P#V,P#V])] = None )
                      ( implicit wpo: WellPartialOrdering[P#State]): DepthBoundedTransition[P] = {
    new DepthBoundedTransition[P](id, lhs, rhs, h, hk, inh)(wpo)
  }
}
