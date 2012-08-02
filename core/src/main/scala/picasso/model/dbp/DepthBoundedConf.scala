package picasso.model.dbp

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer}
import picasso.math._
import picasso.math.WellPartialOrdering._
import picasso.graph._


class DepthBoundedConf[P <: DBCT](_edges: Map[P#V, Map[P#EL, Set[P#V]]], label: P#V => P#VL)
extends GraphLike[DBCT,P,DepthBoundedConf](_edges, label) {


  override type Self = DepthBoundedConf[P] 
  override def companion = DepthBoundedConf
  override def labelOf(x: V) = x label

  type Morphism = Map[V, V]
  type Edges = Map[V, Map[EL, Set[V]]]

  def toStringWithIds(prefix: String, ids: Map[V, String]) = {
    def printNode(n : P#V) = {
      "(" + ids(n) + ", " + n.state + ")" + (0 until n.depth).map(_ => "*").mkString("")
    }
    var vs = vertices
    val buffer = new scala.collection.mutable.StringBuilder()
    buffer.append(prefix + "\n")
    for ( (a,b,c) <- edges ) {
      vs = vs - a - c
      val suffix = if (b.toString != "") (" [" + b + "]\n") else "\n"
      buffer.append("    " + printNode(a) + " -> " + printNode(c) + suffix)
    }
    for ( alone <- vs ) {
      buffer.append("    node " + printNode(alone) + "\n")
    }
    buffer.toString
  }

  //override def toString = toGraphviz("DBC")
  override def toString = {
    val namer = new Namer
    val nodeIds = vertices.map(v => (v, namer("n").replace("$","_"))).toMap[P#V, String]
    toStringWithIds("DepthBoundedConf", nodeIds)
  }

  // use def instead of val if caching requires too much space
  lazy val undirectedAdjacencyMap = this.undirect

  /*
  protected def propagate(ms: MorphState[P], i : Int, j : Int) = {
    val (tableSmaller, tableBigger, nodesSmaller, nodesBigger, compatible) = ms
    val v = nodesSmaller(i)
    val vSucc = undirectedAdjacencyMap(v)
    val w = nodesBigger(j)

    for (k <- i+1 until nodesSmaller.size; if (compatible(k) contains j)) {
      val u = nodesSmaller(k)
      val uSucc = undirectedAdjacencyMap(u)
      val common = vSucc & uSucc
      if (common.exists(n => compatible(tableSmaller(n)).forall(l => nodesBigger(l).depth >= w.depth)))
        compatible.update(k, compatible(k) - j)
    }

    //Logger("TEST", LogNotice, "common: " + common)
    //Logger("TEST", LogNotice, "v: " + v)
    //Logger("TEST", LogNotice, "u: " + u)
    //Logger("TEST", LogNotice, "mergeable: " + merge)
  }
  */
  // use def instead of val if caching requires too much space
  lazy val sameHeightCC: Map[V,Set[V]] = {
    val undir = this.undirect
    val maxDepth = vertices.map(_.depth).reduceLeft(math.max)
    //Console.println("maxDepth = " + maxDepth)
    val bindings = for (d <- 0 to maxDepth) yield {
      val g = undir.filterNodes(_.depth == d)
      val sccs = g.SCC(true)
      //Console.println("d = " + d + ", sccs = " + sccs + " g = " + g)
      for (scc <- sccs; s <- scc) yield (s -> scc)
    }
    val map: Map[V,Set[V]] = bindings.flatten.toMap
    assert(map.keySet == vertices, map.mkString("", ", ", ""))
    map
  }

  protected def additionalCstr(mi: MorphInfo[P]): Iterable[Clause[(V,V)]] = {
    //goal: whatever smaller (this) can do by unfolding, bigger can also do it ...
    val (bigger, candidatesF, candidatesB) = mi
    //(1) difference of depth (good for unit propagation)
    val depthCstr: Iterable[Clause[(V,V)]] = for(x <- vertices.toSeq; y <- candidatesF(x) if (x.depth > y.depth)) yield {
      val lit: Lit[(V,V)] = Neg(x -> y)
      val cl: Clause[(V,V)] = Seq(lit)
      cl
    }

    //TODO not nesting difference but nesting gradient
    //what seems bad about the current version is that is it not symmetric wrt the edge direction (condition in the if)
    //it should rather be something like if one increase, the other should also increase, ...
    //this part should be independent of the flattening (not true now)

    //(2) preserve nesting gradient to preserve the fact that a link is either:
    // one-to-one, one-to-many, many-to-one.
    val deltaDepth: Iterable[Iterable[Clause[(V,V)]]] =
      for((x1, el, y1) <- edges;
          (x2:V) <- candidatesF(x1);
          (y2:V) <- candidatesF(y1)
         ) yield {
        val d1 = y1.depth - x1.depth
        val d2 = y2.depth - x2.depth
     
        //assert that the difference is at least the same
        if ((d1 > 0 && d2 <= 0) || (d1 < 0 && d2 >= 0)) {
          Seq[Clause[(V,V)]](Seq(Neg(x1 -> x2), Neg(y1 -> y2))) //cannot be both true at the same time
        } else {
          Seq[Clause[(V,V)]]() //ok
        }
      }
    /* OLD version of deltaDepth
    val deltaDepth: Iterable[Iterable[Clause[(V,V)]]] =
      for((x1, el, y1) <- edges;
          (x2:V) <- candidatesF(x1) if (x1.depth <= x2.depth);
          (y2:V) <- candidatesF(y1) if (y1.depth <= y2.depth)
         ) yield {
      val d1 = y1.depth - x1.depth
      val d2 = y2.depth - x2.depth

      //assert that the difference is at least the same
      if ((d1 > 0 && d2 < d1) || (d1 < 0 && d2 > d1)) {
        Seq[Clause[(V,V)]](Seq(Neg(x1 -> x2), Neg(y1 -> y2))) //cannot be both true at the same time
      } else {
        Seq[Clause[(V,V)]]() //ok
      }
    }
    */

    //TODO depthInjective should be rephrased in term of components ?
    /*
    val smallCmpGraph = decomposeInDisjointComponents
    val bigCmpGraph = bigger.decomposeInDisjointComponents
    val smallNodeToCmp = smallCmpGraph.vertices.iterator.flatMap( cmp => cmp.map(v => (v, cmp)) ).toMap[V, Set[V]]
    val bigNodeToCmp = bigCmpGraph.vertices.iterator.flatMap( cmp => cmp.map(v => (v, cmp)) ).toMap[V, Set[V]]

    //if a node of the cmpt is mapped to the same cmpt, then the other nodes becomes injective ?
    val depthInjective =
      for (cmp1 <- smallCmpGraph.vertices;
           x1 <- cmp1;
           x2 <- candidatesF(x1) ) yield {
        //TODO ..
      }
    */

    //(3) stuff within the same nesting
    val depthInjective: Iterable[Iterable[Clause[(V,V)]]] =
      //x1 to x2 => all connectedAtSameHeight to x2 becomes injective wrt all connectedAtSameHeight x2
      //injective => not more than one true ...
      for(x1 <- vertices.toSeq;// if (x1.depth > 0);
          x2 <- candidatesF(x1) if (x2.depth > 0 && x1.depth <= x2.depth)
         ) yield {
      val trigger: Lit[(V,V)] = Neg(x1 -> x2)
      val sh2 = (bigger.sameHeightCC(x2) - x2).toSeq
      val sh1 = sameHeightCC(x1) - x1
      val x1_x2_cstr: Iterable[Clause[(V,V)]] = sh2.flatMap(y2 => {
        //we needs a set of constraints that says at most 1 of possible is true
        //which means for all pairs of var one is false.
        val possible = candidatesB(y2).filter(sh1 contains _)
        for (i <- possible.indices; j <- i+1 until possible.size) yield {
          (Seq(trigger, Neg(possible(i) -> y2), Neg(possible(j) -> y2)): Clause[(V,V)])
        }
      })
      x1_x2_cstr
    }
    //Console.println(depthCstr.toString)
    //Console.println(deltaDepth.flatten.toString)
    depthCstr ++ deltaDepth.flatten ++ depthInjective.flatten
  }

  def morphisms(bigger: Self, partialMorph: Morphism = Map.empty[V,V])(implicit wpo: WellPartialOrdering[P#State]) : Iterator[Morphism] = 
    lazyMorphismsBySat[P](bigger, _.depth == 0, additionalCstr, partialMorph)

  def morphism(bigger: Self)(implicit wpo: WellPartialOrdering[P#State]) : Option[Morphism] = 
    morphism[P](bigger, _.depth == 0, additionalCstr)

  def subgraphIsomorphism(bigger: Self)(implicit wpo: WellPartialOrdering[P#State]) : Option[Morphism] = 
    morphism[P](bigger, _.depth == 0, additionalCstr)

  def isSubgraphOf(bigger: Self)(implicit wpo: WellPartialOrdering[P#State]) =
    subgraphIsomorphism(bigger).isDefined
  
  def degree(v: V): Int = undirectedAdjacencyMap(v).size

  def getComponent(node: V): Set[V] = {
    val depth = node.depth
    //take all the nodes conntected with depth greater or equal, repeat until fixpoint.
    def process(acc: Set[V], frontier: Set[V]): Set[V] = frontier.headOption match {
      case Some(x) =>
        val next = undirectedAdjacencyMap(x).filter(v => v.depth >= depth && !acc(v))
        process(acc ++ next, (frontier - x) ++ next)
      case None => acc
    }
    process(Set(node), Set(node))
  }

  /** getComponent + parents componements up to the top componement. */
  def getComponentsPyramide(node: V): Seq[Set[V]] = {
    val cmp1 = getComponent(node)
    def process(acc: List[Set[V]], current: Set[V]): List[Set[V]] = {
      //get one level down from the current cmp
      val lowest = current.map(_.depth).min
      val next = current.flatMap(undirectedAdjacencyMap(_)).find(n => n.depth == (lowest - 1))
      next match {
        case Some(v) => 
          val current1 = getComponent(v)
          assert(current subsetOf current1)
          process(current :: acc, current1)
        case None =>
          current :: acc
      }
    }
    process(Nil, cmp1)
  }

  def decomposeInComponents: Seq[Set[V]] = {
    def process(todo: List[V], acc: List[Set[V]]): Seq[Set[V]] = todo match {
      case x :: xs =>
        val cmp = getComponent(x)
        val todo2 = xs.filterNot(cmp(_))
        process(todo2, cmp :: acc)
      case Nil => acc
    }
    process(vertices.toList.sortWith( (a, b) => a.depth > b.depth), Nil)
  }
  
  /* Edges from x to y iff y is part of x. */
  lazy val decomposeInDisjointComponents: DiGraph[GT.ULGT{type V = Set[P#V]}] = {
    val cmps = decomposeInComponents
    val edges = cmps.flatMap( x => cmps.flatMap( y => if (x != y && (y subsetOf x) ) Some(x -> y) else None) )
    def trim(cmp: Set[V]): Set[V] = {
      val minDepth = cmp.map(_.depth).reduceLeft(math.min)
      cmp.filter(_.depth == minDepth)
    }
    val trimedEdges = edges.map{ case (a,b) => (trim(a), trim(b)) }
    val allVertices = cmps.map(trim)
    DiGraph[GT.ULGT{type V = Set[P#V]}](trimedEdges).addVertices(allVertices)
  }

  /** Unfold the nodes in this graph which are replicated and in the codomain of the morphism.
   *  @param smaller the LHS of a transition
   *  @param m a mapping from the LHS to this graph
   */
  def unfoldWithWitness(smaller: Self, m: Morphism): (Self, Morphism, Morphism) = {

    val smallerUndirected = smaller.undirect

    def cloneComponent(graph: Self, nodes: Set[V]): (Self, Morphism) = {
      assert(nodes.forall(_.depth > 0), nodes + "\n" + graph)
      val witness: Map[V, V] = nodes.map( x => (x, x--) ).toMap
      val newNodes = witness.map(_._2)
      val edgesToCopy = graph.edges.filter{ case (a,_,b) => nodes(a) || nodes(b) }
      val copiedEdges = edgesToCopy.map{ case (a,b,c) => (witness.getOrElse(a,a), b, witness.getOrElse(c,c)) }
      val graph1 = graph ++ copiedEdges
      val graph2 = (graph1 /: newNodes)(_ + _)
      (graph2, witness)
    }

    /** "project" the component cmp of graph back to the smaller graph.
     * @param cmp the component
     * @param newM morphism from smaller to graph
     * @param node seed of the component in smaller 
     */
    def componentOnSmaller(cmp: Set[V], newM: Morphism, node: V): Set[V] = {
      //get the neighbors of smallerX and keep the ones that maps to neighbors of x (i.e. cmp)
      //repeat until fixed point is reached.
      def process(acc: Set[V], frontier: Set[V]): Set[V] = frontier.headOption match {
        case Some(x) =>
          val next = smallerUndirected(x).filter(v => cmp(newM(v)) && !acc(v) )
          process(acc ++ next, (frontier - x) ++ next)
        case None => acc
      }
      process(Set(node), Set(node))
    }

    //to get around a bug in the type checker (not precise enough)
    def dummy(set: Set[V], map: Morphism)( entry: (V, V)): (V, V) = {
      var b: V = null
      if (set(entry._1))
        b = map(entry._2)
      else
        b = entry._2
      (entry._1, b)
    }

    //m is not injective, after unfolding it should be.

    //the unfolding should be done on depth 1 (higher depth will follows from the earlier unfolding)

    //witness if from the new graph to the old one (reverse of the usual morphism)
    //TODO migth need to unfold more in some case ...
    def unfold(graph: Self, newM: Morphism, witness: Morphism): (Self, Morphism, Morphism) = {
      val needUnfolding = newM.filter{ case (a,b) => b.depth >= 1 }
      if (needUnfolding.isEmpty) {
        (graph, newM, witness)
      } else {
        val (smallerMinC, minCandidate) = needUnfolding.minBy( a => a._2.depth ) //unfold the low depth first
        val cmps = graph.getComponentsPyramide(minCandidate)
        val relevantCmp = if (cmps.head.exists(_.depth == 0)) cmps.tail else cmps
        val toUnfold = relevantCmp.head
        Logger("DBP", LogDebug, "unfolding : " + smallerMinC + " -> " + minCandidate)
        Logger("DBP", LogDebug, "component is : " + toUnfold.mkString)
        assert(toUnfold.exists(_.depth == 1), "unfolding no depth 1, something might be wrong with the graph: " + graph + "\n" + newM)
        val (graph2, newWitness) = cloneComponent(graph, toUnfold)
        //the newWitness has to be reversed to point in the right direction
        val witness2 = witness ++ newWitness.map{ case (a,b) => (b, witness.getOrElse(a, a)) }
        //compute the component on the smaller graph ...
        val smallerCmp = componentOnSmaller(toUnfold, newM, smallerMinC)
        //use the witness to rewire the nodes
        val newM2: Morphism = newM.map(dummy(smallerCmp, newWitness)).toMap
        unfold(graph2, newM2, witness2)
      }
    }

    Logger("DBP", LogDebug, "unfoldWithWitness: " + this + "\n" + m.mkString("\n"))
    unfold(this, m, Map())
  }
  
  def unfold(smaller: Self, m: Morphism): (Self, Morphism) = {
    Logger("DBP", LogDebug, "unfolding: " + this + " from " + smaller + " with " + m.mkString)
    val (a,b,_) = unfoldWithWitness(smaller, m)
    (a,b)
  }

  def foldWithWitness(implicit wpo: WellPartialOrdering[P#State]): (Self, Morphism) = {
    val iter = this morphisms this

    def loop(accFolded: Self, accFolding: Morphism): (Self, Morphism) = {
      val iter = accFolded morphisms accFolded
      val changes = iter find ( m => {
        val used: Set[V] = (Set.empty[V] /: m)((acc, p) => acc + p._2)
        val redundant = accFolded.vertices &~ used
        !redundant.isEmpty
      })
      changes match {
        case Some(m) =>
          val redundant = (accFolded.vertices /: m.values)(_ - _)
          val accFolded2 = accFolded -- redundant
          val accFolding2: Morphism = accFolding.map[(V,V), Map[V,V]]{ case (a,b) => ( a, m.getOrElse(b,b) ) }
          loop(accFolded2, accFolding2)
        case None => (accFolded, accFolding)
      }
    }

    loop(this, vertices.map(v => (v,v)).toMap[V,V])    
  }

  def fold(implicit wpo: WellPartialOrdering[P#State]): Self = foldWithWitness._1

  def widenWithWitness(newThreads: Set[V]): (Self, Morphism) = {

    //rather than hack one more time, I should first write cleanly what I should do.
    //we get the cmp, some of them (nodes) needs to be pushed up (the newThreads).
    //since we want to preserve (some of) the gradient (higher level cmpt should not be changed)
    //cmpt of higher depth are pushed up transitively to avoid merging with the newly created one
    
    val cmpGraph = decomposeInDisjointComponents
    //println("cmpGraph: " + cmpGraph)
    val processingOrder = cmpGraph.topologicalSort

    val nodeToCmp = cmpGraph.vertices.iterator.flatMap( cmp => cmp.map(v => (v, cmp)) ).toMap[V, Set[V]]

    val cmpGraphRev = cmpGraph.reverse

    val cmpToNonDisjointCmp = {
      val g = cmpGraph.reflexiveTransitiveClosure
      cmpGraph.vertices.iterator.map(v => v -> (Set[V]() /: g(v))(_ ++ _)).toMap
    }

    def getCmpDownTo(node: V, depth: Int): Set[V] = {
      def process(acc: Set[V], frontier: List[Set[V]]): Set[V] = frontier match {
        case x :: xs =>
          val succ = cmpGraphRev(x).filter(_.head.depth >= depth)
          //println("x = " + x)
          //println("succ = " + succ.mkString(", "))
          val acc2 = (acc /: succ)(_ ++ cmpToNonDisjointCmp(_))
          val frontier2 = (xs /: succ)( (acc, s) => s::acc )
          process(acc2, frontier2)
        case Nil => acc
      }
      val start = nodeToCmp(node)
      val res = process(cmpToNonDisjointCmp(start), List(start))
      //println("getCmpDownTo " + node + ", " + depth + " = " + res.mkString(", "))
      res
    }
    
    def processCmp(cmp: Set[V], toWiden: Set[V], threadsInc: Map[V, Int]): (Set[V], Map[V, Int]) = {
      val (inCmp, rest) = toWiden.partition(cmp contains _)
      //compute the list of replicated nodes that are affected by the nodes inCmp
      val curDepth = cmp.head.depth
      assert(cmp forall (_.depth == curDepth))
      val affected = for (n1 <- inCmp;
                          n2 <- undirectedAdjacencyMap(n1) if n2.depth > curDepth;
                          n3 <- getCmpDownTo(n2, curDepth + 1))
                     yield n3 
      //println("cmp: " + cmp)
      //println("inCmp: " + inCmp)
      //println("affected: " + affected)
      val threadsInc2 = (threadsInc /: (inCmp ++ affected))( (acc, n) => acc + ((n, acc(n) + 1): (V,Int)))
      (rest, threadsInc2)
    }

    val defaultTreadsInc = vertices.map(v => (v, 0)).toMap[V,Int]
    val (left, increment) = ( (newThreads, defaultTreadsInc) /: processingOrder )( (acc, cmp) => acc match {
      case (newThreads, threadsInc) => processCmp(cmp, newThreads, threadsInc)
    })
    assert(left.isEmpty)
    //println("increment: " +increment.mkString(", "))
      
    val mapping: Morphism = increment.flatMap[(V,V), Map[V,V]]{ case (v, i) =>
      if (i == 0) {
        None
      } else {
        val v2 = (v /: (0 until i))( (v,_) => v++ )
        Some(v -> v2)
      }
    }
    //flatten
    val tmp = this morph mapping
    val (result, mapping2) = tmp.flatten
    val resultMapping = mapping.map[(V,V), Map[V,V]]{ case (a,b) => (a, mapping2.getOrElse(b, b) ) }
    //println("tmp: " + tmp)
    //println("result: " + result)
    //println("mapping: " + mapping.mkString(", "))
    //println("mapping2: " + mapping2.mkString(", "))
    //println("resultMapping: " + resultMapping.mkString(", "))
    (result, resultMapping)

  }
  
  def widen(newThreads: Set[V]): Self = widenWithWitness(newThreads)._1

  override def clone: (Self, Morphism) = {
    val m = (Map.empty[V,V] /: vertices){ (acc, v) => acc + (v -> v.clone)}
    (this morph m, m)
  }
  
  //after removing some nodes (e.g. inhibitor), the depth of some nodes might be larger than needed.
  //The flattening will try to reduce the depths.
  def flatten: (Self, Morphism) = {
    val cmpGraph = decomposeInDisjointComponents
    val processingOrder = cmpGraph.topologicalSort
    val defaultDepthMap = Map[Set[V], Int]() withDefault (v => if (v.head.depth == 0) 0 else 1)

    val depthMap = (defaultDepthMap /: processingOrder)( (acc, cmp) => {
      val curDepth = acc(cmp)
      val acc2 = if (!acc.contains(cmp)) acc + (cmp -> curDepth) else acc
      val succ = cmpGraph(cmp)
      (acc2 /: succ)( (map, v) => map + (v -> math.max(curDepth + 1, map(v))) )
    })

    val morphism: Morphism = depthMap.flatMap[(V,V), Map[V,V]]{ case (cmp, i) =>
      for (n <- cmp) yield {
        val delta = n.depth - i
        assert(delta >= 0)
        val n2 = (n /: (0 until delta))( (a, _) => a--)
        (n, n2)
      }
    }
    assert(vertices forall (morphism contains _))
    (this morph morphism, morphism)
  }

  //if this methods returns true, then flattening is not required
  //purpose: detect where thing are going wrong (and fix the bugs) rather than flattening all the time
  def noUnneededNesting: Boolean = {
    val revCmpGraph = decomposeInDisjointComponents.reverse
    revCmpGraph.vertices forall ( cmp => {
      val depth = cmp.head.depth
      depth <= 1 || revCmpGraph(cmp).exists(_.head.depth == depth - 1)
    })
  }


}


object DepthBoundedConf extends GraphFactory[DBCT, DepthBoundedConf]{
  override def apply[P <: DBCT](edges: Map[P#V, Map[P#EL, Set[P#V]]], label: P#V => P#VL) = new DepthBoundedConf[P](edges, label)
  def apply[P <: DBCT](edges: Map[P#V, Map[P#EL, Set[P#V]]]): DepthBoundedConf[P] = {
    val label = {(v: P#V) => v label}
    apply[P](edges, label)
  }
  
  def empty[P <: DBCT]: DepthBoundedConf[P] = {
    val label = {(v: P#V) => v label}
    empty[P](label)
  }


  implicit def wellPartiallyOrdered[P <: DBCT](c: DepthBoundedConf[P])(implicit ev: WellPartialOrdering[P#State]) =
    new WellPartiallyOrdered[DepthBoundedConf[P]] {
      def tryCompareTo (that: DepthBoundedConf[P]): Option[Int] = {
        //print("tryCompareTo: ")
        //print("c = " + c)
        //print("that = " + that)
        if (c eq that) Some(0) else
          c morphism that match {
            case Some(_) => 
              that morphism c match {
                case Some(_) => Some(0)
                case None => Some(-1)
              }
            case None => 
              that morphism c match {
                case Some(_) => Some(1)
                case None => None
              }
          } 
      }
      override def < (that: DepthBoundedConf[P]): Boolean = {
        if (c eq that) false else
          c morphism that match {
            case Some(_) => 
              that morphism c match {
                case Some(_) => false
                case None => true
              }
            case None => false
          } 
      }
      override def > (that: DepthBoundedConf[P]): Boolean = {
        if (c eq that) false else
          c morphism that match {
            case Some(_) => false
            case None => 
              that morphism c match {
                case Some(_) => true
                case None => false
              }
          }
      }
      override def <= (that: DepthBoundedConf[P]): Boolean = {
        if (c eq that) true else
          c morphism that match {
            case Some(_) => true
            case None => false
          } 
      }
      override def >= (that: DepthBoundedConf[P]): Boolean = {
        if (c eq that) true else
          that morphism c match {
            case Some(_) => true
            case None => false
          }
      }
    } 
}
