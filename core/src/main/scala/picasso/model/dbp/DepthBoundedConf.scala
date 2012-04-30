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
  lazy val undirectedAdjacencyMap = {
    val out = adjacencyMap mapValues (_.foldLeft(Set.empty[V])((xs, e) => e._2 ++ xs))
    out.foldLeft(out)((acc, p) => p._2.foldLeft(acc)((acc, x) => acc + ((x, acc.getOrElse(x, Set.empty[V]) + p._1))))
  }

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
    val (bigger, candidatesF, candidatesB) = mi
    //(1) difference of depth (good for unit propagation)
    val depthCstr: Iterable[Clause[(V,V)]] = for(x <- vertices.toSeq; y <- candidatesF(x) if (x.depth > y.depth)) yield {
      val lit: Lit[(V,V)] = Neg(x -> y)
      val cl: Clause[(V,V)] = Seq(lit)
      cl
    }
    //(2) preserve nesting difference
    val deltaDepth: Iterable[Iterable[Clause[(V,V)]]] =
      for((x1, el, y1) <- edges;
          (x2:V) <- candidatesF(x1) if (x1.depth <= x2.depth);
          (y2:V) <- candidatesF(y1) if (y1.depth <= y2.depth)
         ) yield {
      val d1 = y1.depth - x1.depth
      val d2 = y2.depth - x2.depth

      //TODO this seems fixed ...

      //goal: whatever smaller (this) can do by unfolding, bigger can also do it ...
      //see test "subgraph 01"
      //=> should we rather think in term of components ?

      //if increase (d1 > 0), increase at least the same ?
      //if decrease (d1 < 0), decrease at most the same ?
      //that is not very symmetric ? or is it ?
      //due to the flattening the amount of increase and decrease is not that meaningful ...
      //Can it be as simple as preserving the signum ?

      /*
      if (math.signum(d1) == math.signum(d2)) {
        Seq[Clause[(V,V)]]() //ok
      } else {
        Seq[Clause[(V,V)]](Seq(Neg(x1 -> x2), Neg(y1 -> y2))) //cannot be both true at the same time
      }
      */
      //assert that the difference is at least the same
      if ((d1 > 0 && d2 < d1) || (d1 < 0 && d2 > d1)) {
        Seq[Clause[(V,V)]](Seq(Neg(x1 -> x2), Neg(y1 -> y2))) //cannot be both true at the same time
      } else {
        Seq[Clause[(V,V)]]() //ok
      }
    }
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

  protected def getComponent1(undirected: Self, node: V): Set[V] = {
    val depth = node.depth
    //take all the nodes conntected with depth greater or equal, repeat until fixpoint.
    def process(acc: Set[V], frontier: Set[V]): Set[V] = frontier.headOption match {
      case Some(x) =>
        val next = undirected(x).filter(v => v.depth >= depth && !acc(v))
        process(acc ++ next, (frontier - x) ++ next)
      case None => acc
    }
    process(Set(node), Set(node))
  }

  def getComponent(node: V): Set[V] = {
    val undirected = this.undirect
    getComponent1(undirected, node)
  }

  /** getComponent + parents componements up to the top componement. */
  def getComponentsPyramide(node: V): Seq[Set[V]] = {
    val undirected = this.undirect
    val cmp1 = getComponent1(undirected, node)
    def process(acc: List[Set[V]], current: Set[V]): List[Set[V]] = {
      //get one level down from the current cmp
      val lowest = current.map(_.depth).min
      val next = current.flatMap(undirected(_)).find(n => n.depth == (lowest - 1))
      next match {
        case Some(v) => 
          val current1 = getComponent1(undirected, v)
          assert(current subsetOf current1)
          process(current :: acc, current1)
        case None =>
          current :: acc
      }
    }
    process(Nil, cmp1)
  }

  def decomposeInComponents: Seq[Set[V]] = {
    val undirected = this.undirect
    def process(todo: List[V], acc: List[Set[V]]): Seq[Set[V]] = todo match {
      case x :: xs =>
        val cmp = getComponent1(undirected, x)
        val todo2 = xs.filterNot(cmp(_))
        process(todo2, cmp :: acc)
      case Nil => acc
    }
    process(vertices.toList.sortWith( (a, b) => a.depth > b.depth), Nil)
  }
  
  def decomposeInDisjointComponents: DiGraph[GT.ULGT{type V = Set[P#V]}] = {
    val cmps = decomposeInComponents
    val edges = cmps.flatMap( x => cmps.flatMap( y => if (y subsetOf x) Some(x -> y) else None) )
    val directEdges = edges.filter{ case (a,b) => a.head.depth == b.head.depth - 1 }
    def trim(cmp: Set[V]): Set[V] = {
      val minDepth = cmp.map(_.depth).reduceLeft(math.min)
      cmp.filter(_.depth == minDepth)
    }
    val trimedEdges = edges.map{ case (a,b) => (trim(a), trim(b)) }
    DiGraph[GT.ULGT{type V = Set[P#V]}](trimedEdges)
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

    def loop() : (Self, Morphism) = {
      if (iter.hasNext) { 
        val m = iter.next

        val used: Set[V] = (Set.empty[V] /: m)((acc, p) => acc + p._2)
        val redundant = vertices &~ used
        
        if (redundant.isEmpty) loop()
        else (this -- redundant, m)
      } else (this, Map())
    }

    loop()    
  }

  def fold(implicit wpo: WellPartialOrdering[P#State]): Self = foldWithWitness._1

  def widenWithWitness(newThreads: Set[V]): (Self, Morphism) = {

    def processSeed(depth: Int, newThreads: Set[V], threadsInc: Map[V, V]): Map[V, V] = {
      newThreads find (v => (v.depth == depth) && (depth == 0 || (undirectedAdjacencyMap(v) exists (w => (w.depth == depth) && !(newThreads contains w))))) match {
        case Some(seed) =>
          def processComponent(todo: Set[V], newThreads: Set[V], threadsInc: Map[V, V]): Map[V, V] = {
            todo headOption match {
              case Some(v) => {
                val vInc = v++
                val newTodo = todo ++ (undirectedAdjacencyMap(v) filter (newThreads contains)) - v
                processComponent(newTodo, newThreads - v, threadsInc + (v -> vInc))
              }
              case None =>
                processSeed(depth, newThreads, threadsInc)
            }
          }
          processComponent(Set(seed), newThreads, threadsInc)
        case None => 
          val newThreads1 = newThreads filter (_.depth > depth)
          if (!newThreads1.isEmpty) 
            processSeed(depth + 1, newThreads1, threadsInc)
          else threadsInc
      }
    }

    val mapping = processSeed(0, newThreads, Map.empty[V,V])
    (this morph mapping, mapping)
  }
  
  def widen(newThreads: Set[V]): Self = widenWithWitness(newThreads)._1

  override def clone: (Self, Morphism) = {
    val m = (Map.empty[V,V] /: vertices){ (acc, v) => acc + (v -> v.clone)}
    (this morph m, m)
  }
  
  //after removing some nodes (e.g. inhibitor), the depth of some nodes might be larger than needed.
  //The flattening will try to reduce the depths.
  def flatten: (Self, Morphism) = {
    //look at nodes difference of depth between nodes.
    //a node alone should be of depth 0 or 1
    //a can be of depth i > 1 iff it is linked to a node of depth i-1.

    //how to compute the minimal depth:
    //- get the nodes that are replicated
    val (replicated, other) = vertices.partition(_.depth > 0)
    //- create a set of constraints between nodes: eq
    val eqEdges1 = replicated.toSeq.flatMap(v => this(v).toSeq.filter(_.depth == v.depth).map(v -> _))
    val eqEdges2 = eqEdges1.map{case (a,b) => (b,a) }
    val eqGraph = DiGraph[GT.ULGT{type V = P#V}](eqEdges1 ++ eqEdges2).addVertices(replicated)
    
    //- create a set of constraints between nodes: lt
    val ltEdges = replicated.toSeq.flatMap(v => this(v).toSeq.filter(_.depth > v.depth).map(v -> _))
    val ltGraph = DiGraph[GT.ULGT{type V = P#V}](ltEdges).addVertices(replicated)

    //- merge nodes that are equal
    val sameComponents = eqGraph.SCC(true)
    val mergeCmp = sameComponents.flatMap( cmp => cmp.map(_ -> cmp.head) ).toMap[V, V]
    val ltGraphMerged = ltGraph morph mergeCmp
    
      
    //- topological sort
    val topSort = ltGraphMerged.topologicalSort
    //- greedy: assign depth
    val mergedDepths = (Map[V,Int]() /: topSort)( (acc, v) => {
      val currentDepth = acc.getOrElse(v, 1)
      val successors = ltGraphMerged(v) //have depth of at least currentDepth + 1
      val successorsPlusDepth = successors.map(s => s -> math.max(currentDepth + 1, acc.getOrElse(s, 1)) )
      acc ++ successorsPlusDepth + (v -> currentDepth)
    })
    //- expand to the whole SCC
    val lowerDepth = mergeCmp.map[(V,Int), Map[V,Int]]{ case (v, repr) => v -> mergedDepths(repr) }

    val newDepths = lowerDepth
    val changingDepths = newDepths.filter{ case (a,i) => a.depth != i }
    val morphism: Morphism = changingDepths.map[(V,V), Map[V,V]]{ case (a, i) =>
      val delta = a.depth - i
      assert(delta > 0)
      val a2 = (a /: (0 until delta))( (a, _) => a--)
      (a, a2)
    }
    assert(other.forall(v => !morphism.contains(v)))
    val morphismFull = morphism ++ other.map(x => (x,x) )
    (this morph morphism, morphismFull)
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
