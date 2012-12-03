package picasso.model.dbp

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer}
import picasso.math._
import picasso.math.WellPartialOrdering._
import picasso.graph._


class DepthBoundedTransition[P <: DBCT](val id: String,
                                        val lhs: DepthBoundedConf[P],
                                        val rhs: DepthBoundedConf[P],
                                        val hr: Map[P#V, P#V],
                                        val hk: Map[P#V, P#V],
                                        val inh: Option[(DepthBoundedConf[P], Map[P#V, P#V])] = None,
                                        val lhsID: Map[P#V, String] = Map.empty[P#V, String])
                                       (implicit wpo: WellPartialOrdering[P#State])
extends Transition[DepthBoundedConf[P]] 
{

  type Conf = DepthBoundedConf[P]
  type Morphism = Map[P#V, P#V]


  protected def removeInhibitors(conf: Conf, g: Morphism): Option[(Conf, Set[P#V], Morphism)] = {
    inh match {
      case Some((inhibitor, inhMap)) => {
        //get the mapping of the inhibitor starting form the inhMap
        //val gRestricted = g filter (p => inhibitor.vertices(p._1))
        val gRestricted = g filterKeys (inhMap contains _)
        val partialMorphism: Morphism = gRestricted.map{ case (k,v) => (inhMap(k), v) }.toMap
        val matches = inhibitor.morphisms(conf, partialMorphism) 

        val inhMapRange = inhMap.values.toSet
        val nodesToRemove = inhibitor.vertices.filter(v => !inhMapRange.contains(v))
        var nodeRemoved = Set[P#V]()

        //for each of such match removes the part which is not in the range of inhMap
        val notInhibited = (conf /: matches) {
          (conf, m) =>
            val nodesToRemoveMapped = nodesToRemove.map(m(_))
            val coercedConf = conf -- nodesToRemoveMapped
            nodeRemoved = nodeRemoved ++ nodesToRemoveMapped
            coercedConf
        }
        val (flatConf, flattening) = notInhibited.flatten
        //make sure that the morphism g is still valid after removing the inhibitors
        if ( g.values.forall(v => notInhibited.contains(v) && flattening(v).depth >= v.depth) ) {
          Some( (flatConf, nodeRemoved, flattening) )
        } else {
          None
        }
      }
      case None => Some((conf, Set[P#V](), Map[P#V,P#V]()))
    }
  }


  def applyWithWitness(conf: Conf): Seq[(TransitionWitness[P], Conf)] = {
    val homs = lhs.morphisms(conf)

    //g: lhs -> conf
    //TODO this is not quite monotonic:
    // removing all the matches can lead to a situation where the transition cannot be applied,
    // even though removing some matches can lead to a situation where the transition can still be applied.
    // for the moment, we will assume the transition are 'nice'
    def post(g: Morphism): Option[(TransitionWitness[P], Conf)] = {
      val (conf0, g1, unfolding) = conf.unfoldWithWitness(lhs, g)
      //print("conf1: " + conf1)
      //print("lhs: " + lhs.morph(g1))

      // remove all inhibiting subgraphs from conf0 (monotonicity abstraction)
      for ( (conf1, removedByInhibitor, flattening) <- removeInhibitors(conf0, g1) ) yield {

        // Compute nodes that the transition removes from conf1
        val hkRange = hk.values
        val removed = lhs.vertices.flatMap{v => if((hr isDefinedAt v) || (hkRange exists (_ == v))) Set[P#V]() else Set[P#V](g1(v))}
        //println ("removed: " + removed)
 
        // Frame is conf1 w/o the matched lhs and w/o dangling edges to removed nodes
        val frame = conf1 -- (lhs.morph(g1)) -- removed
        //print("conf1: " + conf1)      
        //print("lhs.morph(g1): " + lhs.morph(g1))      
        //print("removed: " + removed)      
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
        val (post, folding) = postUnfolded.foldWithWitness
        //print("post: " + post)

        //the morphism for the post is f_hr_g1 restricted to the frame + g1_hk_f inverted ?
        val postMorphism0 = (conf1 -- removed).vertices.iterator.map{ case x => (x,f_hr_g1.getOrElse(x,x)) }.toMap[P#V, P#V]
        val postMorphism1 = g1_hk_f.flatMap[(P#V,P#V), Morphism]{ case (a,b) => if (a != b) Some(b -> b) else None}
        
        //Logger("dbp", LogWarning, "conf1: " + conf1)
        //Logger("dbp", LogWarning, "removed: " + removed)
        //Logger("dbp", LogWarning, "lhs.morph(g1): " + lhs.morph(g1))
        //Logger("dbp", LogWarning, "conf1 -- lhs.morph(g1): " + (conf1 -- lhs.morph(g1)))
        //Logger("dbp", LogWarning, "frame: " + frame)
        //Logger("dbp", LogWarning, "(frame morph f_hr_g1): " + (frame morph f_hr_g1))
        //Logger("dbp", LogWarning, "(rhsClone morph g1_hk_f): " + (rhsClone morph g1_hk_f))
        //Logger("dbp", LogWarning, "postUnfolded: " + postUnfolded)
        //Logger("dbp", LogWarning, "postMorphism0: " + postMorphism0)//.map{ case (k,v) => k.label + " -> " + v.label }.mkString(", "))
        //Logger("dbp", LogWarning, "postMorphism1: " + postMorphism1.map{ case (k,v) => k.label + " -> " + v.label }.mkString(", "))
        //Logger("dbp", LogWarning, "g1_hk_f: " + g1_hk_f)
        
        val postMorphism = postMorphism0 ++ postMorphism1
        for ( (k, v) <- postMorphism ) {
          assert(conf1.contains(k), "transition " + id + ": " + k + " not in " + conf1.vertices)
          assert(postUnfolded.contains(v), "transition " + id + ": " + v + " not in " + postUnfolded.vertices)
        }
        val notInDomain = conf1.vertices -- postMorphism.keys
        assert( notInDomain.size == removed.size,
                "transition " + id + ": postMorphism, node not in the domain, expected " + removed.size + " found " + notInDomain.mkString(", "))
        val notInRange = postUnfolded.vertices -- postMorphism.values
        val added = rhs.vertices -- hk.keys -- hr.values
        assert( notInRange.size == added.size,
                "transition " + id + ": postMorphism, node not in the range, expected " + added.size + " found " + notInRange.mkString(", "))

        val witness = new TransitionWitness
        witness.transition = this
        witness.from = conf
        //witness.firstMorhism = g
        witness.unfolding = unfolding
        witness.unfolded = conf0
        //witness.unfoldedMorphism = g1
        witness.inhibitedNodes = removedByInhibitor
        witness.inhibitedFlattening = flattening
        witness.inhibited = conf1
        witness.lhsIDs = lhsID.map[(P#V, String), Map[P#V, String]]{ case (k, v) => (g1(k), v) }
        witness.post = postMorphism
        witness.unfoldedAfterPost = postUnfolded
        witness.folding = folding
        witness.to = post
        
        //assert( post.noUnneededNesting, witness )

        (witness, post)
      }
    }

    homs.flatMap(post).toSeq
  }

  def apply(conf: Conf): Set[Conf] = {
    applyWithWitness(conf).map(_._2).toSet
  }

  //TODO this is not really what should happen:
  //need to check if the LHS match, then that the inhibitor cannot be removed while preserving the match.
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

  override def toString = {
    //give id to nodes
    val allVertices = lhs.vertices ++ rhs.vertices ++ inh.map(_._1.vertices).getOrElse(Set[P#V]())
    val namer = new Namer
    val nodeIds = allVertices.map(v => (v, namer("n").replace("$","_"))).toMap[P#V, String]
    def printMap(m: Map[P#V, P#V]) = {
      val buffer = new scala.collection.mutable.StringBuilder()
      for ( (a,b) <- m ) {
        buffer.append("    " + nodeIds(a) + " -> " + nodeIds(b) + "\n")
      }
      buffer.toString
    }
    "transition \"" + id + "\"\n" +
    lhs.toStringWithIds("pre", nodeIds) +
    rhs.toStringWithIds("post", nodeIds) +
    "==>\n" + printMap(hr) +
    "<==\n" + printMap(hk) +
    (inh match {
      case Some((inGraph, inMap)) => 
        inGraph.toStringWithIds("no", nodeIds) +
        "==>\n" + printMap(inMap)
      case None => ""
    })
    //Misc.docToString(toGraphviz("DBT"))
  }

}

object DepthBoundedTransition {
  def apply[P <: DBCT]( id: String,
                        lhs: DepthBoundedConf[P],
                        rhs: DepthBoundedConf[P],
                        h: Map[P#V, P#V],
                        hk: Map[P#V, P#V] = Map.empty[P#V, P#V],
                        inh: Option[(DepthBoundedConf[P], Map[P#V,P#V])] = None,
                        lhsID: Map[P#V, String] = Map.empty[P#V, String])
                      ( implicit wpo: WellPartialOrdering[P#State]): DepthBoundedTransition[P] = {
    new DepthBoundedTransition[P](id, lhs, rhs, h, hk, inh, lhsID)(wpo)
  }
}
