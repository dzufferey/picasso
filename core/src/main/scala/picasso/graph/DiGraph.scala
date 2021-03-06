package picasso.graph

import scala.collection.immutable.{Map, Stream, Set, BitSet}
import scala.text.Document
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Stats}


//TODO refactor to split this file into multiple components (easier to read an maintains)


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
extends Traceable[P#V,P#EL] with GraphAlgorithms[PB, P, G] {
  self: G[P] =>
  type V = P#V
  type VL = P#VL
  type EL = P#EL
  type Self = G[P]
  type AdjacencyMap = Map[V,Map[EL,Set[V]]]

  protected def companion : GraphFactory[PB, G]
  
  def adjacencyMap = edgeMap

  def edges = for ( (n1,map) <- adjacencyMap; (label, n2Set) <- map; n2 <- n2Set) yield (n1, label, n2)
  
  lazy val vertices: Set[V] = adjacencyMap.keySet

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
    toGraphvizFull(name, prefix, if (inBody == "") Document.empty else Document.text(inBody), idPrefix)

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
  
  /** Returns the list of labels on the edges between v1 and v2. */
  def edgesBetween(v1: V, v2: V): Iterable[EL] = {
    outEdges(v1).flatMap{ case (k, v) => if (v(v2)) Some(k) else None }
  }
    
  def contains(v: V): Boolean = adjacencyMap.contains(v)
  
  def contains(v: V, el: EL, w: V): Boolean = this(v,el).contains(w)
    
  def +(x: V, l: EL, y: V): Self = if (contains(x,l,y)) self else companion[P](Labeled.addEdge(adjacencyMap,x,l,y), label)
  def +(x: (V, EL, V)): Self = this + (x._1, x._2, x._3)
  def +(x: V) : Self = if (contains(x)) self else companion[P](adjacencyMap + Pair(x, Map.empty[EL,Set[V]]), label)
  def -(x: V, l: EL, y: V) : Self = if (!contains(x,l,y)) self else companion[P](adjacencyMap + Pair(x, adjacencyMap(x) + Pair(l, adjacencyMap(x)(l) - y)), label)
  def -(v: V) : Self = if (!contains(v)) self else companion[P](adjacencyMap.mapValues(_.mapValues( _ - v)) - v, label)
    
  def --(that: Self) : Self = {
    val (newEdges0, newVertices) = 
      ((Map.empty[V,Map[EL,Set[V]]], Set.empty[V]) /: adjacencyMap){(acc, p) => 
        val (p_newEdges, newVertices) = ((Map.empty[EL,Set[V]], acc._2) /: p._2){(acc, e) => 
          val e_newRange = e._2 -- that(p._1,e._1)
          if (e_newRange.isEmpty) acc else (acc._1 + (e._1 -> e_newRange), acc._2 ++ e_newRange)}
        if (p_newEdges.isEmpty && that.contains(p._1)) acc
        else (acc._1 + (p._1 -> p_newEdges), newVertices)} 
    val newEdges = (newEdges0 /: newVertices){(acc, v) => if (acc isDefinedAt v) acc else acc + (v -> Map.empty[EL,Set[V]])}
    companion[P](newEdges, label)
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
  
  def addVertices(vs: Traversable[V]): Self = (this /: vs)(_ + _)

  def filterNodes(fct: V => Boolean): Self = {
    val toRemove = vertices.filterNot(fct)
    this -- toRemove
  }
  
  def filterEdges(fct: ((V,EL,V)) => Boolean): Self = {
    val toRemove = edges.filterNot(fct)
    (this /: toRemove)( (acc,e) => acc.-(e._1, e._2, e._3) )
  }

  def inducedSubgraph(nodes: Set[V]): Self = filterNodes(nodes contains _)

  def outDegree(v: V): Map[EL, Int] = adjacencyMap(v).mapValues(_.size)
  def outDegreeAll: Map[V, Int] = adjacencyMap.map{case (v, m) => (v, m.values.foldLeft(0)( (acc,set) => acc + set.size )) }

  def edgesWith(v: V) = edges.filter{case (n1,l,n2) => n1 == v || n2 == v}

  def isSymmetric = edges forall { case (a,b,c) => contains(c, b, a) }

  def isAntiReflexive = vertices forall (v => !apply(v).contains(v))

  def isTraceValid(t: Trace[V,EL]): Boolean = {
    val startExists = contains(t.start)
      
    t.transitions.foldLeft((t.start, startExists))((acc, nextStep) => {
      val nextNode = acc._1
      val validPrefix = acc._2
      (nextStep._2, validPrefix && this(nextNode, nextStep._1)(nextStep._2))
    })._2
  }
  
  def morph(morphNode: PartialFunction[V, V]): Self = {
    val morphNodeTotal = morphNode orElse ({case v => v}: PartialFunction[V,V])
    val morphEdge: EL => EL = (el => el)
    morphFull[P](morphNodeTotal, morphEdge, label)
  }
  
  def morphFull[Q <: PB](morphNode: V => Q#V, morphEdge: EL => Q#EL, labels: Q#V => Q#VL): G[Q] = {
    val nodes = vertices map morphNode
    val newEdges = edges.map{ case (a,b,c) => (morphNode(a), morphEdge(b), morphNode(c)) }
    companion[Q](Labeled.listToMap(nodes, newEdges), labels)
    /*
    //TODO cannot use: groupBy[K](f: ((A, B)) => K): Map[K, Map[A, B]] 
    val groupedMap = adjacencyMap groupBy (ves => morphNode(ves._1))
    val morphedMap = groupedMap map { 
      case (v1, edges) =>
        val groupedEdges = edges flatMap (_._2.toList) groupBy (es => morphEdge(es._1))
        val morphedEdges = groupedEdges map { 
          case (el1, dests) => 
            val morphedDests: Set[Q#V] = (Set.empty[Q#V] /: dests)((acc, e) => acc ++ (e._2 map morphNode))
            el1 -> morphedDests
          }
        v1 -> morphedEdges
      }
    val res = companion(morphedMap, labels)
    assert(isSymmetric == res.isSymmetric)
    res
    */
  }

  sealed abstract class Lit[A]
  case class Pos[A](atom: A) extends Lit[A]
  case class Neg[A](atom: A) extends Lit[A]
  type Clause[A] = Seq[Lit[A]]

  type MorphInfo[Q <: PB] = (
    G[Q], //bigger
    P#V => Seq[Q#V], //candidateF
    Q#V => Seq[P#V] //candidatesB
  )

  /** computes morphisms from this to bigger.
   * @param bigger
   * @param injective tell whether multiple nodes can be mapped to a node of bigger
   * @param additionalCstr take the bigger graph and returns some additional constraints on the morphism
   * @param partialMorphism a mapping that serves as stub
   */
  protected def lazyMorphismsBySat[Q <: PB](
    bigger: G[Q],
    injective : Q#V => Boolean,
    additionalCstr: MorphInfo[Q] => Iterable[Clause[(P#V,Q#V)]],
    partialMorphism: Map[P#V,Q#V] = Map.empty[P#V,Q#V]
  )(implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Iterator[Map[P#V,Q#V]] = Stats("lazyMorphismsBySat.encoding", {
    Logger("graph", LogDebug, "Is\n"+this+"a subgraph of\n"+bigger)
    ///////////////////////////////////////////////////
    import org.sat4j.specs.ContradictionException
    import org.sat4j.tools.ModelIterator
    import org.sat4j.core.VecInt
    import org.sat4j.minisat.SolverFactory
    import org.sat4j.tools.ClausalCardinalitiesDecorator
    ///////////////////////////////////////////////////
    val pairToInt = scala.collection.mutable.HashMap[(P#V,Q#V), Int]()
    val intToPair = scala.collection.mutable.HashMap[Int, (P#V,Q#V)]()
    var litCounter = 0
    def p_to_q(p: P#V, q: Q#V) = {
      val pair = (p, q)
      pairToInt.getOrElseUpdate(pair, {
        litCounter += 1
        intToPair += (litCounter -> pair)
        litCounter
      })
    }
    def clauseConvert(c: Clause[(P#V, Q#V)]): VecInt = {
      val asInt = c.map{
        case Pos((p,q)) => p_to_q(p,q)
        case Neg((p,q)) => -p_to_q(p,q)
      }
      new VecInt(asInt.toArray)
    }
    ///////////////////////////////////////////////////
    //compatible is too weak and we need some additional constraints:
    def compatible(p: P#V, q: Q#V): Boolean = lblOrd.lteq(labelOf(p), bigger.labelOf(q))
    val candidatesF: Map[P#V, Seq[Q#V]] = this.vertices.map(p => p -> bigger.vertices.toSeq.filter(compatible(p, _))).toMap
    val candidatesB: Map[Q#V, Seq[P#V]] = bigger.vertices.map(q => q -> this.vertices.toSeq.filter(compatible(_, q))).toMap
    //list of constraints of type \sum_q x_{pq} = 1, that guarantees that each node if mapped to another.
    val fullMapping = vertices.toSeq.map( p => clauseConvert(candidatesF(p).map(q => Pos((p, q)))))
    //list of constraints of type \sum_q x_{pq} <= 1, that guarantees that the mapping is injective (when needed).
    val injectivity = bigger.vertices.filter(injective).toSeq.map(q => candidatesB(q).map(p => Pos((p, q)))).filterNot(_.isEmpty).map(clauseConvert)
    //edges constraints: trigger => one of the alternative is true
    val edgeCstrs1 = for (p <- vertices.toSeq; q <- candidatesF(p)) yield {
      val trigger = Neg(p -> q)
      for ((el, xs) <- outEdges(p).toSeq;
           x <- xs) yield {
        clauseConvert(trigger +: bigger(q, el).filter(compatible(x,_)).map(y => Pos(x -> y)).toSeq)
      }
    }
    val edgeCstrs = edgeCstrs1.flatten
    //partialMorphism
    assert(partialMorphism.keySet subsetOf this.vertices)
    assert(partialMorphism.values forall bigger.vertices)
    val startCstr = for ((p,q) <- partialMorphism) yield clauseConvert(Array(Pos(p, q)))
    //additional constraints
    val mi = (bigger, candidatesF(_), candidatesB(_))
    val addCstr = additionalCstr(mi).map(clauseConvert)
    //Feed the constraints to SAT4J
    val solver = SolverFactory.newDefault();
    solver.setTimeoutOnConflicts(solver.getTimeout())//HACK: avoid the creation of a timer
    solver.newVar(litCounter + 1)
    solver.setExpectedNumberOfClauses(fullMapping.size + injectivity.size + edgeCstrs.size + startCstr.size)
    try {
      Logger("graph", LogDebug, "SAT dictionary:\n" + pairToInt.mkString("  ","\n  ","\n") +
                                "SAT clause (fullMapping):\n" + fullMapping.mkString("  ","\n  ","\n") +
                                "SAT clause (injectivity):\n" + injectivity.mkString("  ","\n  ","\n") +
                                "SAT clause (edgeCstrs):\n" + edgeCstrs.mkString("  ","\n  ","\n") +
                                "SAT clause (startCstr):\n" + startCstr.mkString("  ","\n  ","\n") +
                                "SAT clause (additionalCstr):\n" + addCstr.mkString("  ","\n  ",""))
      for (sumTo1 <- fullMapping) solver.addExactly(sumTo1, 1)
      for (atMost1 <- injectivity) solver.addAtMost(atMost1, 1)
      for (clause <- edgeCstrs) solver.addClause(clause)
      for (clause <- startCstr) solver.addClause(clause)
      for (clause <- addCstr) solver.addClause(clause)
      //val writer = new java.io.PrintWriter(Console.out)
      //solver.printInfos(writer, "SAT4J I: ")
      //writer.flush
      //solver.setVerbose(true)
      //pack eveything into an iterator ...
      new Iterator[Map[P#V,Q#V]] {
        var nextTmp: Option[Map[P#V,Q#V]] = None
        var isFalse = false

        private def extractModel = {
          //val writer = new java.io.PrintWriter(Console.out)
          //solver.printStat(writer, "SAT4J S: ")
          //writer.flush
          val intModel = solver.model().filter(_ >= 0)
          Logger("graph", LogDebug, "SAT model:  " + intModel.mkString("",", ",""))
          try { solver.addBlockingClause(new VecInt(intModel.map(x => -x)))
          } catch { case (_: ContradictionException) => isFalse = true }
          val model = intModel.map(intToPair(_))
          val mapping = model.toMap
          assert(mapping.keySet == vertices)//checks that the mapping is complete
          nextTmp = Some(mapping)
        }

        def hasNext = nextTmp match {
          case Some(_) => true
          case None =>
            Stats("lazyMorphismsBySat.solving", 
              if(!isFalse && solver.isSatisfiable()) {
                extractModel; true
              } else false
            )
        }

        def next() = nextTmp match {
          case Some(mapping) =>
            nextTmp = None
            mapping
          case None =>
            if (hasNext) next
            else throw new java.util.NoSuchElementException("next on empty iterator")
        }
      }
    } catch { case e: ContradictionException =>
      new Iterator[Map[P#V,Q#V]] {
        def hasNext = false
        def next() = throw new java.util.NoSuchElementException("next on empty iterator")
      }
    }
  })

  def morphisms[Q <: PB](bigger: G[Q], injective: Q#V => Boolean, comp: MorphInfo[Q] => Iterable[Clause[(P#V,Q#V)]])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Iterator[Map[V,Q#V]] = 
    (lazyMorphismsBySat(bigger, injective, comp)(lblOrd, ev0, ev1))

  def morphism[Q <: PB](bigger: G[Q], injective: Q#V => Boolean, comp: MorphInfo[Q] => Iterable[Clause[(P#V,Q#V)]])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Option[Map[V,Q#V]] = {
    val iter = morphisms(bigger, injective, comp)(lblOrd, ev0, ev1)
    if (iter.hasNext) Some(iter.next) else None
  }  

  def subgraphIsomorphism[Q <: PB](bigger: G[Q])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Option[scala.collection.Map[V,Q#V]] = {
    val iter = subgraphIsomorphismAll(bigger)
    if (iter.hasNext) Some(iter.next) else None
  }
  
  def subgraphIsomorphismAll[Q <: PB](bigger: G[Q])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Iterator[Map[V,Q#V]] = 
    morphisms(bigger, (_ : Q#V) => true, (_:MorphInfo[Q]) => Nil)(lblOrd, ev0, ev1)


  def isSubgraphOf[Q <: PB](bigger: G[Q])
  (implicit lblOrd: PartialOrdering[VL], ev0: Q#VL =:= P#VL, ev1: P#EL =:= Q#EL) : Boolean =
    subgraphIsomorphism(bigger)(lblOrd, ev0, ev1).isDefined

  def reverse: Self = {
    val revEdges: Iterable[(V, EL, V)] =
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
    companion[P](map4, label)
  }
  
  def undirect: Self = this ++ this.reverse

  /** WARNING: this function finishes only if the set of labels returned by appendLabel is finite
   * @param appendLabel a function to compute the labels of the added edges
   */
  def transitiveClosure(appendLabel: (EL, EL) => EL): Self = {
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

  def reflexiveTransitiveClosure(appendLabel: (EL, EL) => EL, defaultLabel: EL): Self = {
    (this.transitiveClosure(appendLabel) /: vertices)( (acc, v) => acc + ((v,defaultLabel,v)))
  }

  /** returns the set of nodes reachable starting from a node following any edge. */
  def nodesReachableFrom(n: V): Set[V] = {
    def process(from: V, seen: Set[V]): Set[V] = {
      (seen /: this(from))( (acc, to) => {
        if (acc(to)) acc
        else process(to, acc + to)
      })
    }
    process(n, Set.empty[V])
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
  def apply[P <: GT](es: Iterable[(P#V,P#EL,P#V)], label: P#V => P#VL) = new LabeledDiGraph(listToMap(es), label)
  /*def apply[A, B, C](label: A => B) = new LabeledDiGraph[A,B,C](Map.empty[A,Map[C,Set[A]]], label)
  def apply[A, B, C](nodes: Iterable[A], es: Iterable[(A,C,A)], label: A => B) = new LabeledDiGraph[A,B,C](listToMap(nodes, es), label)
  */
}

class EdgeLabeledDiGraph[P <: GT.ELGT](_edges: Map[P#V,Map[P#EL,Set[P#V]]])
extends GraphLike[GT.ELGT,P,EdgeLabeledDiGraph](_edges, ((_: P#V) => ()) ) {
  
  override def nodeToString(n: V): String = n.toString
  override def edgeToString(n1:V, l: P#EL, n2: V): String = n1 + "-" + l + "->" + n2
  override val toStringPrefix = "ELDG"

  override def companion = EdgeLabeledDiGraph
}

object EdgeLabeledDiGraph extends GraphFactory[GT.ELGT, EdgeLabeledDiGraph] {
  import Labeled._
  def apply[P <: GT.ELGT](edges: Map[P#V,Map[P#EL, Set[P#V]]], label: P#V => P#VL) = new EdgeLabeledDiGraph(edges)
  def apply[P <: GT.ELGT](edges: Map[P#V,Map[P#EL, Set[P#V]]]): EdgeLabeledDiGraph[P] = apply(edges)
  def empty[P <: GT.ELGT]: EdgeLabeledDiGraph[P] = empty[P]((x : P#V) => ())
  def apply[P <: GT.ELGT](es: Iterable[(P#V,P#EL,P#V)]) = new EdgeLabeledDiGraph[P](listToMap(es))
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

class DiGraph[P <: GT.ULGT](_edges: Map[P#V,Map[P#EL,Set[P#V]]], label: P#V => P#VL)
extends GraphLike[GT.ULGT,P,DiGraph](_edges, ((x: P#V) => ())) {
  
  override def nodeToString(n: V): String = n.toString
  override def edgeToString(n1:V, l: Unit, n2: V): String = n1 + "-->" + n2
  override val toStringPrefix = "DG"

  override def companion = DiGraph

  def contains(x: V, y: V): Boolean = contains(x, (), y)
  
  def transitiveClosure: DiGraph[P] = transitiveClosure((_, _) => ())
  def reflexiveTransitiveClosure: DiGraph[P] = reflexiveTransitiveClosure((_, _) => (), ())

  /** Compute a minimal coloring of the graph.
   *  @param cutOff the cutOff tells the solver to stop if the solution is at least as good as that value.
   *  The graph needs to be undirected/symmetric and anti-reflexive.
   *  Warning: this method can very very expensive ...
   *  TODO this encoding is bad, there are a lot of symmetry (permuation of the colors). So the solver blows-up (see pigeon hole problem)
   *  TODO a way to fix this to force that the ordering on the color respects the vertices index. 
   */
  def minimalColoring(cutOff: Int): Map[V, Int] = {
    assert(isAntiReflexive && isSymmetric)
    Logger("graph", LogDebug, "minimalColoring for a graph of size " + vertices.size)
    //  create a set of colors (as many as there are vertices)
    //  create constraints: conflict + node has exactly one color
    //  create objective fct: as few variables as possible
    //  extract the solution
    // http://www.sat4j.org/maven23/org.sat4j.maxsat/apidocs/index.html
    import org.sat4j.specs.ContradictionException
    import org.sat4j.maxsat._
    import org.sat4j.core.VecInt
    val colors = 0 until vertices.size
    val solver = new MinCostDecorator(SolverFactory.newDefault())
    solver.setTimeoutOnConflicts(solver.getTimeout())//HACK: avoid the creation of a timer
    val nbrVar = vertices.size * (vertices.size + 1) / 2 + vertices.size
    solver.newVar(nbrVar)
    val assignToVar = scala.collection.mutable.HashMap[(V,Int), Int]()
    val colorUsed = scala.collection.mutable.HashMap[Int, Int]()
    var varCounter = 0
    //populate the variable maps
    for ((v,idx) <- vertices.zipWithIndex; c <- 0 to idx) {
      varCounter += 1
      assignToVar += ((v, c) -> varCounter)
    }
    val assignMax = varCounter
    for (c <- colors) {
      varCounter += 1
      colorUsed += (c -> varCounter)
    }
    assert(varCounter == nbrVar, varCounter + " == " + nbrVar)
    //each vertex has exactly one color:
    for ((v, idx) <- vertices.zipWithIndex) {
      val sumTo1 = Array.ofDim[Int](idx + 1)
      for (c <- 0 to idx) sumTo1(c) = assignToVar(v -> c)
      solver.addExactly(new VecInt(sumTo1), 1)
    }
    //the conflicts:
    val seen = scala.collection.mutable.HashSet[(V,V)]()
    for ( (a,_,b) <- edges if !seen(a -> b)) {
      seen += (b -> a) //since the conflicts are not directed
      for (c <- colors;
           ac <- assignToVar.get(a -> c);
           bc <- assignToVar.get(b -> c)) {
        solver.addAtMost(new VecInt( Seq(ac, bc).toArray), 1)
      }
    }
    //the constraints for the minimisation
    for (c <- colors) {
      solver.setCost(colorUsed(c), 1)
      for (v <- vertices;
           vc <- assignToVar.get(v -> c)) {
        solver.addClause(new VecInt( Seq(-vc, colorUsed(c) ).toArray))
      }
    }
    //solve
    var isSatisfiable = false
    val startTime = java.lang.System.currentTimeMillis
    var model: Array[Int] = null
    var opt = cutOff + 1
    try {
      while (opt > cutOff && solver.admitABetterSolution()) {
        if (!isSatisfiable) {
          if (solver.nonOptimalMeansSatisfiable()) {
            if (solver.hasNoObjectiveFunction()) {
              Logger.logAndThrow("graph", LogError, "solver.hasNoObjectiveFunction()")
            }
            Logger("graph", LogDebug, "MAXSAT problem is satisfiable")
          }
          isSatisfiable = true
        }
        model = solver.model()
        opt = solver.getObjectiveValue().intValue
        Logger("graph", LogDebug, "MAXSAT problem has a solution of " + opt)
        Logger("graph", LogDebug, "MAXSAT problem, optimizing further")
        solver.discardCurrentSolution();
      }
      if (!isSatisfiable) {
        Logger.logAndThrow("graph", LogError, "MAXSAT problem for coloring has no solution.")
      }
    } catch { case _: ContradictionException =>
      if (isSatisfiable) {
        Logger("graph", LogDebug, "MAXSAT problem optimum found.")
      } else {
        Logger.logAndThrow("graph", LogError, "solver has raised ContradictionException.")
      }
    }
    val stopTime = java.lang.System.currentTimeMillis
    Logger("graph", LogDebug, "MAXSAT problem optimum found in " + ((stopTime - startTime) / 1000))
    //get the solution from the model
    val assignPart = model.filter(l => l > 0 && l <= assignMax )
    val varToAssign: Map[Int,(V,Int)] = assignToVar.map{ case(a,b) => (b,a) }.toMap
    val assign = assignPart map varToAssign
    val assignMap = assign.toMap
    assert(assignMap.size == vertices.size)
    assignMap
  }
  def minimalColoring: Map[V, Int] = minimalColoring(-1)

  protected def smallColoring1(
        affinity: (V, V) => Int = (_,_) => 0,
        varToColor: scala.collection.mutable.HashMap[V, Int],
        colorToVar: scala.collection.mutable.HashMap[Int, List[V]]
      ): Seq[Set[V]] = {

    assert(isAntiReflexive, "graph not anti-reflexive")
    assert(isSymmetric, "graph not symmetric: " + edges.filter{ case (a,_,b) => !contains(b, a) })
    Logger("graph", LogDebug, "small coloring for a graph of size " + vertices.size)// + "\n" + this.toString)

    //TODO in large sparse graphs, this is the bottleneck
    val averageAffinity = {
      var sum = 0
      val vertSeq = vertices.toSeq
      val size = vertSeq.size
      for (i <- 0 until size; j <- i+1 until size) {
        sum += affinity(vertSeq(i), vertSeq(j))
      }
      val total = (size * (size - 1)) / 2
      if (total > 0) sum.toDouble / total.toDouble
      else 0
    }

    var newColor = if (colorToVar.isEmpty) 0 else (colorToVar.keysIterator.max + 1)

    //now coloring the rest
    val toColor = vertices -- varToColor.keysIterator
    for (v <- toColor) {
      val conflicting: Set[Int] = apply(v).flatMap(varToColor get _)
      val available = (0 until newColor).filterNot( conflicting contains _ )
      if (available.isEmpty) {
        varToColor += (v -> newColor)
        colorToVar += (newColor -> (v :: colorToVar.getOrElse(newColor, Nil)))
        newColor += 1
      } else {
        val (c, score) = available.view.map(c => {
          val others = colorToVar(c)
          (c, others.view.map(v2 => affinity(v, v2)).max)
        }).maxBy(_._2)
        if(score >= averageAffinity) {
          varToColor += (v -> c)
          colorToVar += (c -> (v :: colorToVar.getOrElse(c, Nil)))
        } else {
          varToColor += (v -> newColor)
          colorToVar += (newColor -> (v :: colorToVar.getOrElse(newColor, Nil)))
          newColor += 1
        }
      }
    }
    
    //return the coloring
    val groups = colorToVar.values.map(_.toSet).toSeq
    Logger("graph", LogDebug, "small coloring has size " + groups.size)
    //Logger("graph", LogDebug, "small coloring is " + groups)
    assert(vertices forall (v => groups exists (_ contains v)))
    assert(groups.forall(g => {
        //println("group: " + g.mkString)
        g.forall(x => {
            //println("x = " + x + ", this(x) = " + this(x))
            g.forall(y => {
                //println("y = " + y)
                !contains(x,y)
            })
        })
    }), "invalid coloring")
    groups
  }

  def smallColoringFromSeed( affinity: (V, V) => Int = (_,_) => 0,
                             partialColoring: Seq[Set[V]]
                           ) : Seq[Set[V]] = {
    //check that the partial coloring is valid:
    //-each node appears only once
    assert(partialColoring.flatten.toSet.size == (0 /: partialColoring)(_ + _.size), "smallColoring: some node has two colors -> " + partialColoring)
    //-no group with and edge
    assert(partialColoring.forall(same => same.forall(x => same.forall(y => !apply(x).contains(y)))), "smallColoring: partialColoring has conflicts.")

    val varToColor = scala.collection.mutable.HashMap[V, Int]()
    val colorToVar = scala.collection.mutable.HashMap[Int, List[V]]()
    var newColor = 0
    
    //seeding the coloring
    for (same <- partialColoring) {
      for (v <- same) varToColor += (v -> newColor)
      colorToVar += (newColor -> same.toList)
      newColor += 1
    }
    
    smallColoring1(affinity, varToColor, colorToVar)
  }

  /** Compute a small coloring of the graph using heuristics.
   *  The graph needs to be undirected/symmetric and anti-reflexive.
   *  Optional arguments:
   *  - affinity: given two nodes returns a guess on whether they should use the same color (higher = better)
   *  - largeClique: a large clique in the graph (used to seed the coloring)
   *  returns the groups of nodes that have the same color
   *  TODO in parallel for large graphs (10k nodes)
   */
  def smallColoring( affinity: (V, V) => Int = (_,_) => 0,
                     largeClique: Set[V] = Set()
                     ): Seq[Set[V]] = {
    val varToColor = scala.collection.mutable.HashMap[V, Int]()
    val colorToVar = scala.collection.mutable.HashMap[Int, List[V]]()
    var newColor = 0
    
    //seeding the coloring
    for (v <- largeClique) {
      varToColor += (v -> newColor)
      colorToVar += (newColor -> (v :: colorToVar.getOrElse(newColor, Nil)))
      newColor += 1
    }
    
    smallColoring1(affinity, varToColor, colorToVar)
  }

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

