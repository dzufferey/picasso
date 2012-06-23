package picasso.graph

import scala.collection.immutable.{Map, Stream, Set, BitSet}
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}

trait GraphAlgorithms[PB <: GT, P <: PB, G[P1 <: PB] <: GraphLike[PB, P1, G]] {
  self: G[P] =>
 
  def shortestPathOpt(x: V, y: V): Option[Trace[V,EL]] = {
    val visited = new scala.collection.mutable.HashSet[V]()
    val toProcess = new scala.collection.mutable.Queue[V]()
    val pred = new scala.collection.mutable.HashMap[V,(V,EL)]()
    def findY: List[V] = {
      val n = toProcess.dequeue
      if (visited(n)) {
        findY
      } else if (n == y) {
        //get path to x
        def getPath(current: V, acc: List[V]): List[V] = {
          if (current == x) x::acc
          else getPath(pred(current)._1, current::acc)
        }
        getPath(y, Nil)
      } else {
        visited += n
        val succ: Map[EL,Set[V]] = adjacencyMap(n)
        succ.foreach( p => p._2 foreach ( m => {
          toProcess.enqueue(m)
          if (!pred.contains(m)) pred += Pair(m,(n,p._1))
        }))
        findY
      }
    }
    if (!contains(x)) Logger.logAndThrow("graph", LogError, x + " is not part of the graph")
    if (!contains(y)) Logger.logAndThrow("graph", LogError, y + " is not part of the graph")
    toProcess.enqueue(x)
    try {
      val lst = findY
      val start = lst.head
      val trs = lst.tail.map( x => (pred(x)._2,x))
      Some(Trace[V,EL](start, trs:_*))
    } catch { case _: java.util.NoSuchElementException => None }
  }

  def shortestPath(x: V, y: V): Trace[V,EL] = {
    shortestPathOpt(x, y).getOrElse(Logger.logAndThrow("graph", LogError, y+" is unreachable from "+x+"."))
  }

  def shortestObservablePath(x: V, y: V): Trace[VL,EL] = {
    val trace = shortestPath(x,y)
    Trace[VL,EL](labelOf(trace.start), trace.transitions.map( p => (p._1, labelOf(p._2))):_*)
  }

  /** Compute an abstract interpretation fixpoint.
   * @param post the function that computes the post (action on an edge). post shoulde be monotonic.
   * @param join join (associative and commutative)
   * @param cover covering test (_ \geq _)
   * @param defaultValue the initial abstract values
   */
  def aiFixpoint[D](post: (D, EL) => D,
                    join: (D, D) => D,
                    cover: (D,D) => Boolean,
                    defaultValue: V => D,
                    forceMonotonicity: Boolean = false
                   ): Map[V, D] = {
    import scala.collection.parallel.immutable.ParMap
    import scala.collection.parallel.immutable.ParIterable
    //initialisation
    var fp2 = ParMap[P#V, D]( vertices.toSeq.map(v => (v -> defaultValue(v)) ) :_* )
    var fp1 = fp2
    val workLists = ParMap[P#V, ParIterable[(P#V,P#EL,P#V)]]( vertices.toSeq.map(v => (v -> edges.par.filter( _._3 == v) )) :_* )
    /*
    for (v <- vertices) {
      fp2 += (v -> defaultValue(v))
      fpTemp += (v -> scala.collection.mutable.ListBuffer[D]())
    }
    */
    //big while loop
    var iteration = 0
    do {
      iteration += 1
      Logger("graph", LogDebug, "AI, status at begining of iteration " + iteration + ":\n" + fp2.mkString("\n"))
      //(1) copy fp2 into fp1
      fp1 = fp2
      //(2) compute the next iteration
      fp2 = workLists.map{ case (c, edges) =>
        edges.view.map{ case (a,b,c) => post(fp1(a), b) }.reduceOption(join) match {
          case Some(joined) =>
            if(forceMonotonicity) {
              (c, join(joined, fp1(c)))
            } else {
              assert(cover(joined, fp1(c)), "not monotonic @ "+c+": new " + joined + ", old " + fp1(c)) //make sure it is increasing
              (c, joined)
            }
          case None => (c -> fp1(c))
        }
      }
      //Console.println("iteration: fp1 = " + fp1)
      //Console.println("iteration: fp2 = " + fp2)
    } while (fp1 exists { case (v,d) => !cover(d, fp2(v)) })
    //return the result
    fp1.seq
  }
  
  def aiFixpointBackward[D](pre: (D, EL) => D,
                            join: (D, D) => D,
                            cover: (D,D) => Boolean,
                            defaultValue: V => D,
                            forceMonotonicity: Boolean = false
                           ): Map[V, D] =
    this.reverse.aiFixpoint(pre, join, cover, defaultValue, forceMonotonicity)

  /** Strongly connected component decomposition */
  def SCC(all: Boolean): List[Set[V]] = {
    //tarjan's SCC algorithm
    var index = 0
    val stack = new scala.collection.mutable.Stack[V]()
    val indices = new scala.collection.mutable.HashMap[V,Int]()
    val lowlink = new scala.collection.mutable.HashMap[V,Int]()
    var scc: List[Set[V]] = Nil

    def tarjan(v : V): Unit = {
      indices += v -> index
      lowlink += v -> index
      index += 1
      stack.push(v)
      for (vp <- apply(v)) {
        if(! indices.isDefinedAt(vp)) {
          tarjan(vp)
          lowlink += v -> scala.math.min(lowlink(v), lowlink(vp))
        } else if (stack.contains(vp)) {
          lowlink += v -> scala.math.min(lowlink(v), indices(vp))
        }
      }
      // we have a SCC
      if(lowlink(v) == indices(v)) {
        var cc = Set[V]()
        var vp = v
        do {
          vp = stack.pop
          cc = cc + vp
        } while (vp != v)
        scc = cc :: scc
      }
    }

    for (i <- vertices)
      if (! indices.isDefinedAt(i))
        tarjan(i)

    scc.filter( cc => all || cc.forall( x => apply(x).exists(  y => cc.contains(y) )))
  }
  def SCC: List[Set[V]] = SCC(false)
  /** scc or single node from which you cannot escape */
  def bottomSCC = SCC(true).filter(cc => cc.forall( x => apply(x).forall(  y => cc.contains(y) )))
  
  /** Returns a decomposition of the graphs into simple pathes.
   *  A simple spath is a path without loop. Furthermore, the decomposition
   *  is such that a state is either an extremity of possibly multiple pathes
   *  or within a single path.
   */
  def simplePaths: List[Trace[V,EL]] = {
    // (1) tags node with multiple input and multiple outputs
    val outDegree = this.outDegreeAll
    val inDegree =  this.reverse.outDegreeAll
    val (connections, inner) = this.vertices.partition( n => {
      val in = inDegree(n)
      val out = outDegree(n)
      !(in == 1 && out == 1)
    })
    // (2) starts to builds the path (and remove non extremity nodes as they are used)
    def findPath(connections: Set[V], outDegree: Map[V, Int], graph: Self): Trace[V,EL] = {
      val start = connections.find(n => outDegree(n) > 0).get
      def pickNext(v: V): (EL, V) = {
        val (label, nextSet) = graph.outEdges(v).find{case (_, set) => !set.isEmpty}.get
        val next = nextSet.head
        (label, next)
      }
      def dfs(from: V): Trace[V, EL] = {
        val (label, next) = pickNext(from)
        if (connections(next)) Trace(from, (label -> next))
        else dfs(next).prepend(from, label)
      }
      dfs(start)
    }
    // (3) Given a path remove the internal nodes
    def pruneGraph( trace: Trace[V,EL],
                    connections: Set[V],
                    inDegree: Map[V, Int],
                    outDegree: Map[V, Int],
                    graph: Self):
                  (Set[V], Map[V, Int], Map[V, Int], Self) = {
      val internal = trace.states.drop(1).dropRight(1)
      assert(internal forall (inner.contains))
      val triples = trace.triples
      val (a1,l1,b1) = triples.head
      val (a2,l2,b2) = triples.last
      val outDegree2 = outDegree + (a1 -> (outDegree(a1) - 1)) + (a2 -> (outDegree(a2) - 1)) -- internal
      val inDegree2 = inDegree + (b1 -> (inDegree(b1) - 1)) + (b2 -> (inDegree(b2) - 1)) -- internal
      val graph2 = graph -- internal - (a1,l1,b1) - (a2,l2,b2)
      val (uselessConnections, rest) = connections partition (n => outDegree2(n) == 0 && inDegree2(n) == 0)
      ( rest,
        inDegree2 -- uselessConnections,
        outDegree2 -- uselessConnections,
        graph2 -- uselessConnections )
    }
    // (4) the big while loop
    def loop(connections: Set[V], inDegree: Map[V, Int], outDegree: Map[V, Int], graph: Self, acc: List[Trace[V,EL]]): List[Trace[V,EL]] = {
      if (connections.isEmpty) acc
      else {
        val path = findPath(connections, outDegree, graph)
        val (connections2, inDegree2, outDegree2, graph2) = pruneGraph(path, connections, inDegree, outDegree, graph)
        loop(connections2, inDegree2, outDegree2, graph2, path :: acc)
      }
    }
    loop(connections, inDegree, outDegree, this, Nil)
  }
  
  /** algorithm from "Finding all the elementary cycles of a directed graph" by Donald B. Johnson, 1975 */
  def elementaryCycles: Seq[Trace[V,EL]] = {

    //TODO as an iterator rather than a Seq
    //since the number cycles of is quite large it might make sense to do it lazily

    val nodeOrder = vertices.zipWithIndex.toMap
    val idToNode: Map[Int, V] = nodeOrder.map( x => (x._2, x._1) )
    var acc: List[List[V]] = Nil

    def circuit(least: V, subgraph: Self) {
      import scala.collection.mutable._
      val blocked = HashSet[V]()
      var blocked2 = HashMap[V,HashSet[V]]()
      val stack = Stack[V]()

      def unblock(v: V) {
        blocked -= v
        val b2 = blocked2.getOrElse(v, HashSet[V]())
        blocked2 += (v -> HashSet[V]())
        b2 foreach unblock
      }

      def dfs(v: V): Boolean = {
        stack.push(v)
        blocked += v
        var cycleFound = false
        for (w <- subgraph(v)) {
          if (w == least) {
            //we have a cycle
            cycleFound = true
            val trace = least :: stack.toList
            acc = trace :: acc
          } else if (!blocked(w)) {
            cycleFound = dfs(w)
          }
        }
        if (cycleFound) {
          unblock(v)
        } else {
          for (w <- subgraph(v)) {
            val b2 = blocked2.getOrElse(w, HashSet[V]())
            b2 += v
            blocked2 += (w -> b2)
          }
        }
        stack.pop
        cycleFound
      }

      dfs(least)
    }

    var sccs = SCC
    var n = 0
    while (n < nodeOrder.size && !sccs.isEmpty) {
      val leastSCC = sccs.minBy(scc => nodeOrder(scc.minBy(nodeOrder)))
      sccs = sccs.filterNot(_ == leastSCC)
      val subgraph = this.inducedSubgraph(leastSCC)
      val leastNode = leastSCC.minBy(nodeOrder)
      circuit(leastNode, subgraph)
      sccs = (subgraph - leastNode).SCC ++ sccs
    }

    def mkRevTrace(revNodes: List[V]): List[Trace[V, EL]] = revNodes match {
      case x :: Nil => List(Trace[V,EL](x))
      case Nil => Logger.logAndThrow("graph", LogError, "elementaryCycles: empty trace.")
      case x :: y :: xs =>
        val stubs = mkRevTrace(y :: xs)
        val labels = edgesBetween(y, x).toList
        assert(!labels.isEmpty, revNodes + "\n" + this)
        labels.flatMap( l => stubs.map( t => t.prepend(x, l)) )
    }

    (acc flatMap mkRevTrace) map (_.reverse)
  }

}
