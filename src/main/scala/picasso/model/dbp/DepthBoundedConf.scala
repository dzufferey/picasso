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
  type UndirectedAdjacencyMap = Map[V, Set[V]]

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
      assert(nodes.forall(_.depth > 0))
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
    def unfold(graph: Self, newM: Morphism, witness: Morphism): (Self, Morphism, Morphism) = newM.find{ case (a,b) => b.depth == 1 } match {
      case Some((smallerX, x)) =>
        val cmp = graph.getComponent(x)
        Logger("DBP", LogDebug, "unfolding : " + smallerX + " -> " + x)
        Logger("DBP", LogDebug, "component is : " + cmp.mkString)
        val (graph2, newWitness) = cloneComponent(graph, cmp)
        val witness2 = witness ++ newWitness.map{ case (a,b) => (b, witness.getOrElse(a, a)) } //the newWitness has to be reversed to point in the right direction

        //compute the component on the smaller graph ...
        val smallerCmp = componentOnSmaller(cmp, newM, smallerX)
        Logger("DBP", LogDebug, "smaller component is : " + smallerCmp.mkString)
        //use the witness to rewire the nodes
        val newM2: Morphism = newM.map(dummy(smallerCmp, newWitness)).toMap

        unfold(graph2, newM2, witness2)
      case None =>
        val complexUnfolding = newM.filter(_._2.depth > 0)
        if (complexUnfolding.isEmpty) {
          (graph, newM, witness)
        } else {
          assert(false, "if we get here the system is probably not depth-bounded!")
          //if there are still some mapping with degree strictly more than one, 
          //get the componements in which is the node up to depth 1, and unfold the component.
          //TODO when this part is stable, it can take over the special case above (subsumes it)
          val (smallerMinC, minCandidate) = complexUnfolding.minBy( a => a._2.depth )
          val cmps = graph.getComponentsPyramide(minCandidate)
          val relevantCmp = if (cmps.head.exists(_.depth == 0)) cmps.tail else cmps
          def unfoldPyramide(cmps: Seq[Set[V]], graph: Self, accM: Morphism, accWitness: Morphism): (Self, Morphism, Morphism) = {
            if (cmps.isEmpty) {
              (graph, accM, accWitness)
            } else {
              assert(cmps.head.exists(_.depth == 1), "unfolding no depth 1, something might be wrong with the graph: " + graph + "\n" + accM)
              val (graph2, newWitness) = cloneComponent(graph, cmps.head)
              //the newWitness has to be reversed to point in the right direction
              val witness2 = accWitness ++ newWitness.map{ case (a,b) => (b, accWitness.getOrElse(a, a)) }
              //compute the component on the smaller graph ...
              val smallerCmp = componentOnSmaller(cmps.head, accM, smallerMinC)
              //use the witness to rewire the nodes
              val accM2: Morphism = accM.map(dummy(smallerCmp, newWitness)).toMap
              val cmps2 = cmps.tail.map(cmp => cmp.map(n => newWitness.getOrElse(n, n) ))
              unfoldPyramide(cmps2, graph2, accM2, witness2)
            }
          }
          unfoldPyramide(relevantCmp, graph, newM, witness)
        }
    }

    Logger("DBP", LogDebug, "unfoldWithWitness")
    unfold(this, m, Map())
  }
  
  def unfold(smaller: Self, m: Morphism): (Self, Morphism) = {
    Logger("DBP", LogDebug, "unfolding: " + this + " from " + smaller + " with " + m.mkString)
    val (a,b,_) = unfoldWithWitness(smaller, m)
    (a,b)
  }

  /*
  def unfold(smaller: Self, m: Morphism): (Self, Morphism) = {
    
    val smallerAdj = smaller.undirectedAdjacencyMap

    val biggerAdj = this.undirectedAdjacencyMap

    def unfold(m: Morphism, biggerAdj: UndirectedAdjacencyMap, bigger: Edges): (Morphism, Edges) = {
      def copyComponent(new_m: Morphism, todo : List[(Option[V], V)], cloneMap: Map[V, V]) : (Morphism, UndirectedAdjacencyMap, Edges) = {
        val totalCloneMap = (x: V) => cloneMap.getOrElse(x,x)
        todo match {
          case Nil => {
            // Duplicate edges for cloned nodes
            val new_bigger: Edges = {
              val old_new_edges: Edges =
                bigger.map[(V,Map[EL, Set[V]]),Edges](p => {
                  val y = p._1
                  val es = p._2
                  if (!(cloneMap isDefinedAt y)) (y, es mapValues (ys => ys ++ (ys collect cloneMap)))
                  else (y, es)})
              val cloned_new_edges: Edges = 
                bigger.collect[(V,Map[EL, Set[V]]),Edges] 
                  {case (y, es) if cloneMap isDefinedAt y => (cloneMap(y), es mapValues (ys => ys map totalCloneMap))}
              old_new_edges ++ cloned_new_edges
            }
            val new_biggerAdj: UndirectedAdjacencyMap = 
              (biggerAdj.map[(V,Set[V]),UndirectedAdjacencyMap] (p => {
                val y = p._1
                val y1s = p._2
                if (!(cloneMap isDefinedAt y)) (y, y1s ++ (y1s collect cloneMap))
                else (y, y1s)})) ++
              biggerAdj.collect[(V,Set[V]),UndirectedAdjacencyMap] {case (y, y1s) if cloneMap isDefinedAt y => (cloneMap(y), y1s map totalCloneMap)}
            (new_m, new_biggerAdj, new_bigger)
          }
          case (opt_x, y) :: todo1 => {
            if ((cloneMap contains y) || y.depth == 0) {
              val new_m1 = 
                opt_x match {
                  case None => new_m
                  case Some(x) => new_m + ((x, totalCloneMap(y)))
                }
              copyComponent(new_m1, todo1, cloneMap) 
            } else {
              val y_clone = y--
              val new_cloneMap = cloneMap + ((y, y_clone))
              val new_m1 = 
                opt_x match {
                  case None => new_m
                  case Some(x) => new_m + ((x, y_clone))
                }
              val todo_left =
                opt_x match {
                  case None => Nil
                  case Some(x) =>
                    (smallerAdj(x) map (x1 => (Some(x1), m(x1)))) toList
                }
              val todo_right = (biggerAdj(y) map ((None, _))) toList
              val new_todo = todo_left ++ todo1 ++ todo_right
              copyComponent(new_m1, new_todo, new_cloneMap)
            }
          }
        }
      }

      // pick seed node in some replication component
      val seed = m find (_._2.depth > 0)
      
      seed match {
        case None => (m, bigger)
        case Some(p) => {
          val new_acc = copyComponent(m, List((Some(p._1), p._2)), Map.empty[V,V])
          unfold(new_acc._1, new_acc._2, new_acc._3)
        }
      }
    }

    val res = unfold(m, biggerAdj, adjacencyMap)
    (DepthBoundedConf[P](res._2), res._1)
  }
  */

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
