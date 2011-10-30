package picasso.graph

import scala.collection.immutable.{Map, Stream, Set, BitSet}
import scala.text.Document
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import scala.annotation.tailrec

object Labeled {
  
  def addEdge[A,B](edges: Map[A,Map[B,Set[A]]], x: A, l: B, y: A): Map[A,Map[B,Set[A]]] = {
    val withY = if (edges.contains(y)) edges else edges + Pair(y, Map.empty[B,Set[A]])
    if (withY.contains(x))
      if (withY(x).contains(l))
        if (withY(x)(l).contains(y)) withY
        else withY + Pair(x, withY(x) + Pair(l, withY(x)(l) + y))
      else withY + Pair(x, withY(x) + Pair(l, Set.empty[A] + y))
    else withY + Pair(x, Map.empty[B,Set[A]] + Pair(l, Set.empty[A] + y))
  }

  def listToMap[A,B](es: Traversable[(A,B,A)]): Map[A,Map[B,Set[A]]] =
    es.foldLeft(Map.empty[A,Map[B,Set[A]]])( (acc, edge) => addEdge(acc, edge._1, edge._2, edge._3) )
  
  def listToMap[A,B](nodes: Traversable[A], es: Traversable[(A,B,A)]): Map[A,Map[B,Set[A]]] =
    nodes.foldLeft(listToMap(es))( (acc, x) => if (acc.contains(x)) acc else acc + Pair(x, Map.empty[B,Set[A]]))

}


abstract class GT {
  type V
  type VL
  type EL
}

/* TODO: PB should be contravariant. This would enable a non-flat hierarchy of graph classes */
trait GraphFactory[PB <: GT, G[P1 <: PB] <: GraphLike[PB, P1, G]] {
  def apply[P1 <: PB](edges: Map[P1#V, Map[P1#EL, Set[P1#V]]], label: P1#V => P1#VL): G[P1]
  def empty[P1 <: PB](label: P1#V => P1#VL) = apply(Map.empty[P1#V, Map[P1#EL, Set[P1#V]]], label)
}

/** A generic directed graph with labels on the edges and the nodes.
 *  V is the type of the vertices,
 *  VL is the type of the vertex labels, and
 *  EL is the type of the edges label.
 */
/* TODO: PB should be contravariant. This would enable a non-flat hierarchy of graph classes */
abstract class GraphLike[PB <: GT, P <: PB, G[P1 <: PB] <: GraphLike[PB, P1, G]](edgeMap: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL)
extends Traceable[P#V,P#EL] {
  self: G[P] =>
  type V = P#V
  type VL = P#VL
  type EL = P#EL
  type Self = G[P]
  type AdjacencyMap = Map[V,Map[EL,Set[V]]]

  protected def companion : GraphFactory[PB, G]
  
  def adjacencyMap = edgeMap

  def edges = for ( (n1,map) <- adjacencyMap; (label, n2Set) <- map; n2 <- n2Set) yield (n1, label, n2)
  
  def vertices: Set[V] = adjacencyMap.keysIterator.foldLeft(Set.empty[V])(_ + _)

  def nbrVertices = adjacencyMap.size

  def labelOf(v: V) = label(v)

  protected def nodeToString(v: V): String = v.toString + "(" + labelOf(v) + ")"
  protected def edgeToString(v: V, el: EL, w: V): String = v + "-" + el + "->" + w
  protected val toStringPrefix = "G"

  override def toString = {
    toStringPrefix + "{\n" +
    "  nodes: " + vertices.iterator.map(nodeToString).addString(new StringBuilder, ", ") + "\n" +
    "  edges: " + edges.addString(new StringBuilder, ", ") + "\n" +
    "}\n"
  }


  /**
   * @param name the name of the graph
   * @param prefix "digraph"
   * @param inBody stuff to add in the body of the graph
   * @param idPrefix prefix the ids of the node (to avoid scoping clashes)
   * @param nodeProps a function that return some properties of the node (prop=value)
   * @param edgeProps a function that return some properties of the edge (prop=value)
   */
  def toGraphvizExplicit(name: String,
                         prefix: String,
                         inBody: Document,
                         idPrefix: String,
                         nodeProps: V => List[(String,String)],
                         edgeProps: EL => List[(String,String)]): (Document, Map[V, String]) = {
    import Document._
    val (id, _) = vertices.foldLeft((Map.empty[V,String],0))((acc, v) => (acc._1 + (v -> Misc.quoteIfFancy(idPrefix + acc._2)), acc._2 + 1))
    def docOfProps(lst: List[(String,String)]) = lst.map{ case (p,s) => text(p) :: "=" :: text(s) }.reduceRight(_ :: "," :: _)
    def nodeProps2(v: V) = {
      val p1 = nodeProps(v)
      if (p1.find(_._1 == "label").isDefined) p1
      else ("label", Misc.quote(if (labelOf(v)==()) v.toString else labelOf(v).toString)) :: p1
    }
    def nodeToDoc(v: V) = id(v).toString :: " [":: docOfProps(nodeProps2(v)) :: text("];")
    def edgeProps2(e: EL) = {
      val p1 = edgeProps(e)
      if (p1.find(_._1 == "label").isDefined || e == ()) p1
      else ("label", Misc.quote(e.toString)) :: p1
    }
    def edgeToDoc(a:V, b:EL, c: V) = {
      val props = edgeProps2(b)
      val body = if (props.isEmpty) text(";") else " [":: docOfProps(props) :: text("];")
      id(a).toString :: " -> " :: id(c).toString :: body
    }
    val nodesDoc = vertices map nodeToDoc
    val nodes = if (nodesDoc.isEmpty) empty: Document else nodesDoc.reduceRight((v, acc) => v :/: acc)
    val edgesDoc = edges map { case (a,b,c) => edgeToDoc(a, b, c) }
    val edgesStr = if(edgesDoc.isEmpty) empty else edgesDoc.reduceRight((e, acc) => e :/: acc )
    val header = if (inBody == empty) empty else (empty :/: inBody)
    val dot = prefix :: " " :: Misc.quoteIfFancy(name) :: " {" :: nest(4, header :/: nodes :/: edgesStr) :/: text("}")
    (dot, id)
  }

  def toGraphvizFull(name: String, prefix: String, inBody: Document, idPrefix: String): (Document, Map[V, String]) =
    toGraphvizExplicit(name, prefix, inBody, idPrefix, _ => Nil, _ => Nil)
  def toGraphvizFull(name: String, prefix: String, inBody: String, idPrefix: String): (Document, Map[V, String]) =
    toGraphvizFull(name, prefix, Document.text(inBody), idPrefix)

  def toGraphvizDoc(name: String = toStringPrefix, prefix: String = "digraph"): Document = 
    toGraphvizFull(name, prefix, "", "")._1

  def toGraphviz(name: String): String = Misc.docToString(toGraphvizDoc(name))

  /** Returns the set of successors */
  def apply(v: V, el: EL): Set[V] = {
    if (adjacencyMap.contains(v)) {
      val map2 = adjacencyMap(v)
      if (map2.contains(el)) map2(el)
      else Set.empty[V]
    }
      else Set.empty[V]
  }

  /** Returns the set of successors, without looking at the labels */
  def apply(v: V): Set[V] = (adjacencyMap get v) map (m => (Set.empty[V] /: m.values)(_++_)) getOrElse Set.empty[V]

  /** Returns the set of vertices that have the given label */
  def get(el: VL): Set[V] = adjacencyMap.keysIterator.foldLeft(Set.empty[V])( (acc, v) => if (labelOf(v) == el) acc + v else acc)

  def outEdges(v: V): Map[EL, Set[V]] = adjacencyMap(v)
    
  def contains(v: V): Boolean = adjacencyMap.contains(v)
  
  def contains(v: V, el: EL, w: V): Boolean = this(v,el).contains(w)
    
  def +(x: V, l: EL, y: V): Self = if (contains(x,l,y)) self else companion(Labeled.addEdge(adjacencyMap,x,l,y), label)
  def +(x: (V, EL, V)): Self = this + (x._1, x._2, x._3)
  def +(x: V) : Self = if (contains(x)) self else companion(adjacencyMap + Pair(x, Map.empty[EL,Set[V]]), label)
  def -(x: V, l: EL, y: V) : Self = if (!contains(x,l,y)) self else companion(adjacencyMap + Pair(x, adjacencyMap(x) + Pair(l, adjacencyMap(x)(l) - y)), label)
  def -(v: V) : Self = if (!contains(v)) self else companion(adjacencyMap.mapValues(_.mapValues( _ - v)) - v, label)
    
  def --(that: Self) : Self = {
    val (newEdges0, newVertices) = 
      ((Map.empty[V,Map[EL,Set[V]]], Set.empty[V]) /: adjacencyMap){(acc, p) => 
        val (p_newEdges, newVertices) = ((Map.empty[EL,Set[V]], acc._2) /: p._2){(acc, e) => 
          val e_newRange = e._2 -- that(p._1,e._1)
          if (e_newRange.isEmpty) acc else (acc._1 + (e._1 -> e_newRange), acc._2 ++ e_newRange)}
        if (p_newEdges.isEmpty) acc else (acc._1 + (p._1 -> p_newEdges), newVertices)} 
    val newEdges = (newEdges0 /: newVertices){(acc, v) => if (acc isDefinedAt v) acc else acc + (v -> Map.empty[EL,Set[V]])}
    companion(newEdges, label)
  }

  def --(vs: Traversable[V]): Self = (this /: vs)(_ - _)

  def ++(moreNodes: Traversable[(V, EL, V)]): Self = (this /: moreNodes)(_ + _)

  def ++(moreEdges: AdjacencyMap) = {
    def merge(es1: Map[EL, Set[V]], es2: Map[EL, Set[V]]) = {
      (es1 /: es2) ((acc, p) => acc + ((p._1, es1.getOrElse(p._1, Set[V]()) ++ p._2)))
    }
    val newVertices = (Map[V,Map[EL,Set[V]]]() /: moreEdges) ((acc, p) => (acc /: p._2) ((acc, p) => (acc /: p._2) ((acc, v) => acc + ((v, Map[EL,Set[V]]())))))

    val newEdges: AdjacencyMap = moreEdges.map[(V,Map[EL,Set[V]]),AdjacencyMap]{p => (p._1, merge(adjacencyMap.getOrElse(p._1, Map[EL,Set[V]]()), p._2))}

    companion[P](newVertices ++ adjacencyMap ++ newEdges, label)
  }

  def ++(that: Self): Self = {
    def merge(es1: Map[EL, Set[V]], es2: Map[EL, Set[V]]) = {
      (es1 /: es2) ((acc, p) => acc + ((p._1, es1.getOrElse(p._1, Set[V]()) ++ p._2)))
    }
      
    val newMap = (adjacencyMap /: (that adjacencyMap)) ((acc, p) => acc + ((p._1, merge(adjacencyMap.getOrElse(p._1, Map[EL,Set[V]]()), p._2))))
    companion[P](newMap, label)
  }

  def outDegree(v: V): Map[EL, Int] = adjacencyMap(v).mapValues(_.size)
  def outDegreeAll: Map[V, Int] = adjacencyMap.map{case (v, m) => (v, m.values.foldLeft(0)( (acc,set) => acc + set.size )) }

  def edgesWith(v: V) = edges.filter{case (n1,l,n2) => n1 == v || n2 == v}

    /*
    def isTraceValid(t: Trace[B,C]): Boolean = {
      def checkNext(current: Set[A], transition: C, target: B): Set[A] = {
        current.foldLeft(Set.empty[A])((acc, c) => (this(c, transition).filter(label(_) == target) ++ acc))
      }
    ! (t.transitions.foldLeft(get(t.start))( (acc, tred) => checkNext(acc, tred._1, tred._2))).isEmpty
    }
    */

  def isTraceValid(t: Trace[V,EL]): Boolean = {
    val startExists = contains(t.start)
      
    t.transitions.foldLeft((t.start, startExists))((acc, nextStep) => {
      val nextNode = acc._1
      val validPrefix = acc._2
      (nextStep._2, validPrefix && this(nextNode, nextStep._1)(nextStep._2))
    })._2
  }
  
 
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

  def morph(morphNode: PartialFunction[V, V]): Self = {
    val morphNodeTotal = morphNode orElse ({case v => v}: PartialFunction[V,V])
    val morphEdge: EL => EL = (el => el)
    morphFull(morphNodeTotal, morphEdge, label)
  }
  
  def morphFull[Q <: PB](morphNode: V => Q#V, morphEdge: EL => Q#EL, labels: Q#V => Q#VL): G[Q] = {
    val groupedMap = adjacencyMap groupBy (ves => morphNode(ves._1))
    val morphedMap = groupedMap map { 
      case (v1, edges) =>
        val groupedEdges = edges flatMap (_._2.toList) groupBy (es => morphEdge(es._1))
        val morphedEdges = groupedEdges map { 
          case (el1, dests) => 
            val morphedDests = (Set.empty[Q#V] /: dests)((acc, e) => acc ++ (e._2 map morphNode))
            el1 -> morphedDests
          }
        v1 -> morphedEdges
      }
    companion(morphedMap, labels)
  }

  protected def mkLookup: (Map[V,Int], IndexedSeq[V]) = {
    val vs: IndexedSeq[V] = vertices.toIndexedSeq
    val table: Map[V,Int] = (Map.empty[V,Int] /: vs.indices)( (table, i) => table + (vs(i) -> i))
    (table, vs)
  }

  //needs a square array of variables:
  //compatibility: same or higher nesting + ordering on the labels
  //cstr:
  // -sum per row is one (all things are mapped)
  // -per column: dont'care of thing with lower nesting, at most one of the same nesting, none of higher nesting
  // -edges: as implication (one mapping => forces (alternative) of other)
  //         forall p, q, p mapped to q => that neighbors of p gets mapped to neighbors of q with appropriate label on the edge

  /** computes morphisms from this to bigger.
   * @param bigger
   * @param injective tell whether multiple nodes can be mapped to a node of bigger
   * @param partialMorphism a mapping that serves as stub
   * TODO what about propagate more ?
   */
  protected def lazyMorphisms2[Q <: PB](bigger: G[Q], injective : Q#V => Boolean, partialMorphism: Map[P#V,Q#V] = Map.empty[P#V,Q#V])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Iterator[Map[P#V,Q#V]] = {
    def p_to_q(p: P#V, q: Q#V) = (p, q)
    def compatible(p: P#V, q: Q#V): Boolean = sys.error("TODO")
    def candidatesF(p: P#V): Seq[Q#V] = bigger.vertices.filter(compatible(p, _)).toSeq
    def candidatesB(q: Q#V): Seq[P#V] = this.vertices.filter(compatible(_, q)).toSeq
    //list of constraints of type \sum_q x_{pq} = 1, that guarantees that each node if mapped to another.
    val fullMapping: Iterable[Iterable[(P#V,Q#V)]] = vertices.toSeq.map( p => candidatesF(p).map(q => p_to_q(p, q)))
    //list of constraints of type \sum_q x_{pq} = 1, that guarantees that the mapping is injective (when needed).
    val injectivity: Iterable[Iterable[(P#V,Q#V)]] = bigger.vertices.filter(injective).toSeq.map(q => candidatesB(q).map(p => p_to_q(p, q)))
    //edges constraints: trigger => one of the alternative is true
    val edgeCstrs1 = for (p <- vertices.toSeq; q <- candidatesF(p)) yield {
      val trigger = p_to_q(p, q)
      for ((el, xs) <- outEdges(p).toSeq;
           x <- xs) yield {
        (trigger, bigger(q, el).filter(compatible(x,_)).map(y => p_to_q(x,y)))
      }
    }
    val edgeCstrs: Iterable[((P#V,Q#V), Iterable[(P#V,Q#V)])] = edgeCstrs1.flatten
    //partialMorphism
    val startCstr: Iterable[(P#V,Q#V)] = for ((p,q) <- partialMorphism) yield p_to_q(p, q)
    sys.error("TODO send everything into a pseudo-boolean solver")
  }

  //args:
  //smaller (this), bigger, ...

  type MorphState[Q <: PB] = (Map[P#V,Int], Map[Q#V,Int], IndexedSeq[P#V], IndexedSeq[Q#V], Array[BitSet])

  def lazyMorphisms[Q <: PB](bigger: G[Q], injective : Q#V => Boolean, propagateMore: (MorphState[Q], Int, Int) => Unit, partialMorphism: Map[P#V,Q#V] = Map.empty[P#V,Q#V])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Iterator[Map[P#V,Q#V]] = {
    Logger("graph", LogDebug, "Is\n"+this+"a subgraph of\n"+bigger)
    //this is a simple and stupid implementation ...
    
    val vs: Set[Q#V] = bigger.vertices

    //lookup tables for nodes in this
    val (tableSmaller, nodesSmaller) = self.mkLookup
    val sSmaller = nodesSmaller.size
    //lookup tables for nodes in bigger
    val (tableBigger, nodesBigger) = bigger.mkLookup
    val sBigger = nodesBigger.size
    
    //initial compatibility matrix (rough initialisation)
    var compatible = Array.fill(sSmaller){BitSet.empty}
    for (i <- 0 until sSmaller; j <- 0 until sBigger) {
      val ns = nodesSmaller(i)
      val nb = nodesBigger(j)
      val nodeLabel = lblOrd.lteq(labelOf(ns), bigger.labelOf(nb))
      def allInjective(k : Q#EL) = bigger(nb,k).forall(injective(_))
      def biggerOutDegree(s: Map[EL,Int], b: Map[Q#EL,Int]) = {
        s.keysIterator.forall( k => s(k) <= b.getOrElse(k,0) || !allInjective(k))
      }
      val isCompatible = nodeLabel && biggerOutDegree(self.outDegree(ns), bigger.outDegree(nb))
      if (isCompatible) compatible.update(i, compatible(i) + j)
    }

    /*
    def printMatrix : Unit = {
      print("   ")
      for (j <-0 until sBigger) {
        print(j + ":" + bigger.labelOf(nodesBigger(j)) + " ")
      }
      println("")
      for (i <- 0 until sSmaller) {
        print(i + ":" + labelOf(nodesSmaller(i)) + "| ")
        for (j <-0 until sBigger) {
          val e = if (compatible(i)(j)) 1 else 0
          print(e + " ")
        }
        println("")
      }
    }*/

    //refinement procedure
    def refine(i: Int, j: Int): Unit = {
      //this is about neighbors 'compatibility'
      //the choices that have been made restrict the future choices
      val ns = nodesSmaller(i)
      val succs = adjacencyMap(ns)
      val nb = nodesBigger(j)
      val succb = bigger.adjacencyMap(nb)
      //foreach neighbour, there must be at least one possibility to place it,
      //the labels on the edges need to agree.
      val possible = succs.forall( p => {
        val label = p._1
        val candidates = succb.getOrElse(label,Set.empty[Q#V])
        p._2.forall( ss => {
          candidates.exists( sb => compatible(tableSmaller(ss))(tableBigger(sb)) )
        })
      })
      if (!possible) compatible.update(i, compatible(i) - j)
    }

    def propagate = {
      //for all ones in compatible, call refine
      for (i <- 0 until sSmaller; j <- 0 until sBigger if compatible(i)(j)) refine(i,j)
      //TODO much parallelism to exploit (can even be done optimistically (modulo volatile))
      //TODO as a fixpoint
    }
    def isValidPartialMapping = compatible.forall(!_.isEmpty)
    def isValidMapping = compatible.forall( _.size == 1)

    def fixMapping(i: Int, j: Int) {
      val mask: Seq[Int] = for (rest <- j+1 until sBigger) yield rest
      compatible.update(i, compatible(i) -- mask)
      if (injective(nodesBigger(j)))
        for (rest <- i + 1 until sSmaller)
          compatible.update(rest, compatible(rest) - j)
      else propagateMore((tableSmaller, tableBigger, nodesSmaller, nodesBigger, compatible), i, j)
    }


    // fix mappings according to given partial morphism
    partialMorphism foreach {p => fixMapping(tableSmaller(p._1), tableBigger(p._2))}

    //TODO better: not only forward-propagation, but also backjumping
    //main search loop with stack for backtracking.
    propagate
    val stack = new scala.collection.mutable.Stack[Array[BitSet]]

    
    def computeHoms(decisionLevel: Int): (Option[Map[P#V,Q#V]], Int) = {
      //println("DL: " + decisionLevel)
      //printMatrix
      if (! isValidPartialMapping) {
        if (decisionLevel <= 0) (None, decisionLevel)
        else {
          compatible = stack.pop
          val lastTry = compatible(decisionLevel - 1).headOption
          if(!lastTry.isEmpty) compatible.update(decisionLevel - 1, compatible(decisionLevel - 1) - lastTry.get)
          computeHoms(decisionLevel - 1)
        }
      }
      else {
        if (decisionLevel >= sSmaller) {
          assert(isValidMapping)
          val hom = Map.empty[V,Q#V] ++ (for (i <- 0 until sSmaller; j <- 0 until sBigger if compatible(i)(j)) yield ( nodesSmaller(i), nodesBigger(j)) )        
          (Some(hom), decisionLevel)
        } else {
          //pick next
          (0 until sBigger).find( candidate => compatible(decisionLevel)(candidate)) match {
            case Some(j) => {
              stack.push(compatible.clone) //TODO should only clone a subarray + index mapping
              fixMapping(decisionLevel, j)
              propagate
              
              computeHoms(decisionLevel + 1)
            }
            case None => Logger.logAndThrow("graph", LogError, "a valid partial mapping must have a candidate.")
          }
        }
      }
    }
    
    new Iterator[Map[P#V,Q#V]] {
      var (curr, decisionLevel) = computeHoms(0)
      
      def hasNext = curr.isDefined

      def next() = {
        val prev = curr.get
        val (newCurr, newDL) = {
          if (decisionLevel <= 0) (None, decisionLevel)
          else {
            val lastTry = compatible(decisionLevel - 1).headOption
            compatible = stack.pop
            if(!lastTry.isEmpty) compatible.update(decisionLevel - 1, compatible(decisionLevel - 1) - lastTry.get)
            computeHoms(decisionLevel - 1)
          }
        }
        curr = newCurr
        decisionLevel = newDL
        prev
      }
    }
  }

  def morphisms[Q <: PB](bigger: G[Q], injective: Q#V => Boolean, propagate: (MorphState[Q],Int,Int) => Unit)
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Set[Map[V,Q#V]] = 
    (lazyMorphisms(bigger, injective, propagate)(lblOrd, ev0, ev1)).foldLeft(Set.empty[Map[V,Q#V]])(_ + _)

  def morphism[Q <: PB](bigger: G[Q], injective: Q#V => Boolean, propagate: (MorphState[Q],Int,Int) => Unit)
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Option[Map[V,Q#V]] = {
    val iter = lazyMorphisms(bigger, injective, propagate)(lblOrd, ev0, ev1)
    if(iter.hasNext) Some(iter.next) else None
  }  

  def subgraphIsomorphism[Q <: PB](bigger: G[Q])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Option[scala.collection.Map[V,Q#V]] = 
    morphism(bigger, (_ : Q#V) => true, ((_: MorphState[Q],_ ,_)  => ()))(lblOrd, ev0, ev1)


  def isSubgraphOf[Q <: PB](bigger: G[Q])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Boolean =
    subgraphIsomorphism(bigger)(lblOrd, ev0, ev1).isDefined

  /** Returns a topological sort of the graph. */
  def topologicalSort: Seq[V] = {
    import scala.collection.mutable.Queue
    val q = Queue[V]()
    var graph = this.reverse
    while (graph.nbrVertices > 0) {
      //Logger("graph", LogError, "topologicalSort: " + graph)
      val ready = graph.vertices.filter( v => graph(v).isEmpty)
      if (ready.isEmpty) Logger.logAndThrow("graph", LogError, "topologicalSort of a cyclic graph.")
      graph = graph -- ready
      q ++= ready
    }
    q.toSeq
  }

  def reverse: Self = {
    val revEdges: Iterable[(P#V, P#EL, P#V)] =
      for ( (n1,map) <- adjacencyMap;
            (label, n2Set) <- map;
            n2 <- n2Set)
        yield (n2, label, n1)
    val map1 = revEdges groupBy (_._1)
    val map2 = map1 mapValues (_ groupBy (_._2))
    val map3 = map2 mapValues (_ mapValues (iterable => {
          val stripped = iterable map (_._3)
          Set[P#V](stripped.toSeq:_*)
        }))
    val map4 = (map3 /: vertices)( (map, v) => if (! (map contains v)) map + (v -> Map.empty[EL,Set[V]]) else map)
    companion(map4, label)
  }

  /** WARNING: this function finishes only if the set of labels returned by appendLabel is finite
   * @param appendLabel a function to compute the labels of the added edges
   */
  def transitiveClosure(appendLabel: (P#EL, P#EL) => P#EL): Self = {
    //fixpoint algorithm
    val toAdd = new scala.collection.mutable.ListBuffer[(P#V, P#EL, P#V)]()
    for ( v1 <- vertices;
          (l1, v2s) <- adjacencyMap(v1); v2 <- v2s;
          (l2, v3s) <- adjacencyMap(v2); v3 <- v3s) {
      val l3 = appendLabel(l1, l2)
      if (!this(v1,l3)(v3)) toAdd += ((v1,l3,v3))
    }
    if (toAdd.isEmpty) this
    else (this ++ toAdd).transitiveClosure(appendLabel)
  }

  def reflexiveTransitiveClosure(appendLabel: (P#EL, P#EL) => P#EL, defaultLabel: P#EL): Self = {
    (this.transitiveClosure(appendLabel) /: vertices)( (acc, v) => acc + ((v,defaultLabel,v)))
  }


  //TODO is it the best place to put it in ??
  //it would be better in automaton, but it does not depend of anytimg in automaton.

   /** Compute an abstract interpretation fixpoint.
    * @param post the function that computes the post (action on an edge). post shoulde be monotonic.
    * @param join join (associative and commutative)
    * @param cover covering test (_ \geq _)
    * @param defaultValue the initial abstract values
    */
  def aiFixpoint[D](post: (D, P#EL) => D, join: (D, D) => D, cover: (D,D) => Boolean, defaultValue: V => D): Map[V, D] = {
    val fp1 = new scala.collection.mutable.HashMap[P#V, D]()
    val fp2 = new scala.collection.mutable.HashMap[P#V, D]()
    for (v <- vertices) fp2 += (v -> defaultValue(v)) //initialize fp2
    do {
      //(1) copy fp2 into fp1
      for (v <- vertices) fp1 += (v -> fp2(v))
      //(2) compute the next iteration
      for ((a,b,c) <- edges) {
        //Console.println("iteration: edge = " + (a,b,c))
        fp2 += (c -> join(post(fp1(a), b), fp2(c)))
      }
      //Console.println("iteration: fp1 = " + fp1)
      //Console.println("iteration: fp2 = " + fp2)
    } while (vertices exists (v => !cover(fp1(v), fp2(v))))
    fp1.toMap
  }
  
  def aiFixpointBackward[D](pre: (D, P#EL) => D, join: (D, D) => D, cover: (D,D) => Boolean, defaultValue: V => D): Map[V, D] =
    this.reverse.aiFixpoint(pre, join, cover, defaultValue)

  /** Strongly connected component decomposition */
  def SCC: List[Set[V]] = {
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

    scc.filter( cc => cc.forall( x => apply(x).forall(  y => cc.contains(y) )))
  }
  
  /** Returns a decomposition of the automaton into simple pathes.
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

}

case class ProtoEdge[V,EL](src: V, e: EL){
  import Labeled._
 
  def ->(trg: V) = addEdge(Map.empty[V,Map[EL,Set[V]]], src, e, trg)
}

trait VertexLike[Self <: VertexLike[Self]] {
  self: Self => 
    import Labeled._
 
    def -->(that: Self) = addEdge(Map.empty[Self,Map[Unit,Set[Self]]], this, (), that)

    def -[EL](e: EL) = ProtoEdge[Self,EL](this, e)
}

case class Vertex[A](value: A) extends VertexLike[Vertex[A]] {
  override def toString = value.toString
}

object GT {
  type NLGT = GT{type EL = Unit}
  type ELGT = GT{type VL = Unit}
  type ULGT = NLGT{type VL = Unit}
}


class LabeledDiGraph[P <: GT](edges: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL)
extends GraphLike[GT,P,LabeledDiGraph](edges, label) {
  override def companion = LabeledDiGraph
}

object LabeledDiGraph extends GraphFactory[GT, LabeledDiGraph] {
  import Labeled._
  def apply[P <: GT](edges: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL) = new LabeledDiGraph(edges, label)
  /*def apply[A, B, C](label: A => B) = new LabeledDiGraph[A,B,C](Map.empty[A,Map[C,Set[A]]], label)
  def apply[A, B, C](es: Iterable[(A,C,A)], label: A => B) = new LabeledDiGraph[A,B,C](listToMap(es), label)
  def apply[A, B, C](nodes: Iterable[A], es: Iterable[(A,C,A)], label: A => B) = new LabeledDiGraph[A,B,C](listToMap(nodes, es), label)
  */
}

class EdgeLabeledDiGraph[P <: GT.ELGT](edges: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL)
extends GraphLike[GT.ELGT,P,EdgeLabeledDiGraph](edges, label) {
  
  override def nodeToString(n: V): String = n.toString
  override def edgeToString(n1:V, l: P#EL, n2: V): String = n1 + "-" + l + "->" + n2
  override val toStringPrefix = "ELDG"

  override def companion = EdgeLabeledDiGraph
}

object EdgeLabeledDiGraph extends GraphFactory[GT.ELGT, EdgeLabeledDiGraph] {
  import Labeled._
  def apply[P <: GT.ELGT](edges: Map[P#V,Map[P#EL, Set[P#V]]], label: P#V => P#VL) = 
    new EdgeLabeledDiGraph(edges, label)
  def apply[P <: GT.ELGT](edges: Map[P#V,Map[P#EL, Set[P#V]]]): EdgeLabeledDiGraph[P] =
    apply(edges, (x : P#V) => ())
  def empty[P <: GT.ELGT]: EdgeLabeledDiGraph[P] = empty[P]((x : P#V) => ())
  /*def apply[A,C,B](edges: Map[A,Map[B,Set[A]]]) = new EdgeLabeledDiGraph[A,C,B](edges)
  def apply[A,C,B]() = new EdgeLabeledDiGraph[A,C,B](Map.empty[A,Map[B,Set[A]]])
  def apply[A,C,B](es: Iterable[(A,B,A)]) = new EdgeLabeledDiGraph[A,C,B](listToMap(es))
  def apply[A,C,B](nodes: Iterable[A], es: Iterable[(A,B,A)]) = new EdgeLabeledDiGraph[A,C,B](listToMap(nodes, es))
  */
}

object Unlabeled {
  
  def addEdge[A](edges: Map[A,Map[Unit,Set[A]]], x: A, y: A): Map[A,Map[Unit,Set[A]]] = {
    val withY = if (edges contains y) edges else edges + Pair(y, Map.empty[Unit,Set[A]])
    val xOut = withY.getOrElse(x,Map.empty[Unit,Set[A]]).getOrElse((),Set.empty[A])
    if (xOut.contains(y)) withY
    else withY + Pair(x, Map(((), xOut + y)))
  }

  def listToMap[A](nodes: Iterable[A], es: Iterable[(A,A)]): Map[A,Map[Unit,Set[A]]] =
    nodes.foldLeft(listToMap(es))( (acc, x) => if (acc.contains(x)) acc else acc + Pair(x, Map.empty[Unit,Set[A]]))

  def listToMap[A](es: Iterable[(A,A)]): Map[A,Map[Unit,Set[A]]] =
    es.foldLeft(Map.empty[A,Map[Unit,Set[A]]])( (acc, edge) => addEdge(acc, edge._1, edge._2) )
}

class NodeLabeledDiGraph[P <: GT.NLGT](edges: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL)
extends GraphLike[GT.NLGT,P,NodeLabeledDiGraph](edges, label) {
  
  override def nodeToString(n: V): String = n.toString + "(" + labelOf(n) + ")"
  override def edgeToString(n1:V, l: Unit, n2: V): String = n1 + "-->" + n2
  override val toStringPrefix = "NLG"

  override def companion = NodeLabeledDiGraph

  def contains(x: V, y: V): Boolean = contains(x, (), y)

  def transitiveClosure: NodeLabeledDiGraph[P] = transitiveClosure((_, _) => ())
  def reflexiveTransitiveClosure: NodeLabeledDiGraph[P] = reflexiveTransitiveClosure((_, _) => (), ())

  /*override def add(x: A): NodeLabeledDiGraph[A,B] = if (contains(x)) this else NodeLabeledDiGraph(edges + Pair(x,Set.empty[A]), label)
  def remove(x: A, y: A) = if (!contains(x,y)) this else NodeLabeledDiGraph(edges + Pair(x, edges(x) - y), label)
  override def remove(x: A): NodeLabeledDiGraph[A,B] = if (!contains(x)) this else NodeLabeledDiGraph(edges.mapValues(_ - x) - x, label)
  */
}

object NodeLabeledDiGraph extends GraphFactory[GT.NLGT, NodeLabeledDiGraph] {
  import Labeled._
  def apply[P <: GT.NLGT](edges: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL) = new NodeLabeledDiGraph(edges, label)
}

/*
object NodeLabeledDiGraph {
  import Unlabeled._
  def apply[A,B](edges: Map[A,Set[A]], label: A => B) = new NodeLabeledDiGraph[A,B](edges, label)
  def apply[A,B](label: A => B) = new NodeLabeledDiGraph[A,B](Map.empty[A,Set[A]], label)
  def apply[A,B](es: Iterable[(A,A)], label: A => B) = new NodeLabeledDiGraph[A,B](listToMap(es), label)
  def apply[A,B](nodes: Iterable[A], es: Iterable[(A,A)], label: A => B) = new NodeLabeledDiGraph[A,B](listToMap(nodes, es), label)
}
*/

class DiGraph[P <: GT.ULGT](edges: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL)
extends GraphLike[GT.ULGT,P,DiGraph](edges, ((x: P#V) => ())) {
  
  override def nodeToString(n: V): String = n.toString
  override def edgeToString(n1:V, l: Unit, n2: V): String = n1 + "-->" + n2
  override val toStringPrefix = "DG"

  override def companion = DiGraph

  def contains(x: V, y: V): Boolean = contains(x, (), y)
  
  def transitiveClosure: DiGraph[P] = transitiveClosure((_, _) => ())
  def reflexiveTransitiveClosure: DiGraph[P] = reflexiveTransitiveClosure((_, _) => (), ())

}

object DiGraph extends GraphFactory[GT.ULGT, DiGraph]{
  import Unlabeled._
  def apply[P <: GT.ULGT](edges: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL) = new DiGraph(edges, label)
  def apply[P <: GT.ULGT](edges: Map[P#V,Map[P#EL,Set[P#V]]]): DiGraph[P] = 
    apply[P](edges, (x: P#V) => ())
  def empty[P <: GT.ULGT]: DiGraph[P] = apply[P](Map[P#V,Map[P#EL,Set[P#V]]](), (x: P#V) => ())
  def apply[P <: GT.ULGT](es: Iterable[(P#V,P#V)]) = new DiGraph[P](listToMap(es), (x: P#V) => ())
  /*def apply[A](edges: Map[A,Set[A]]) = new DiGraph[A](edges)
  def apply[A]() = new DiGraph[A](Map.empty[A,Set[A]])
  def apply[A](nodes: Iterable[A], es: Iterable[(A,A)]) = new DiGraph[A](listToMap(nodes, es))*/
}

