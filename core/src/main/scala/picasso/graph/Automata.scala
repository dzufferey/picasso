package picasso.graph

import scala.collection.immutable.Set
import scala.collection.immutable.Map
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Level, Misc}


class Automaton[P <: GT.ELGT](edges: Map[P#V,Map[P#EL,Set[P#V]]], val initState: P#V, val targetStates: Set[P#V]) extends EdgeLabeledDiGraph[P](edges) {

  //TODO

  def states = vertices

  def isDeterministic: Boolean = edges.forall( _._2.size <= 1 )

  //probably the method you don't want to call
  //TODO look at antichain based method rather than the standard powerset construction
  def determinize : Automaton[GT.ELGT{type V = Set[P#V]; type EL=P#EL}] = {
    sys.error("TODO")
  }
  
  /** Synchronised product of two automata. */
  def product[P1 <: GT.ELGT{type EL = P#EL}](a: Automaton[P1]): Automaton[GT.ELGT{type V = (P#V, P1#V); type EL = P#EL}] = {
    val init = (initState, a.initState)
    //this needs to be pruned to keep only the states that exists / are reachable
    val targetStates = (Set.empty[(P#V, P1#V)] /: states)( (acc, s1) => (acc /: a.states)( (acc, s2) => acc + (s1 -> s2)))
    //build edges (simulataneous traversal of both automata)
    val queue = new scala.collection.mutable.Queue[(P#V, P1#V)]()
    val seen = new scala.collection.mutable.HashSet[(P#V, P1#V)]()
    val productEdges = new scala.collection.mutable.ListBuffer[((P#V, P1#V), P#EL, (P#V, P1#V))]()
    queue enqueue init
    seen += init
    while (! queue.isEmpty) {
      val (s1, s2) = queue.dequeue
      val succ1 = adjacencyMap.getOrElse(s1, Map.empty[P#EL, Set[P#V]])
      val succ2 = a.adjacencyMap.getOrElse(s2, Map.empty[P#EL, Set[P1#V]])
      val commonKeys = succ1.keySet intersect succ2.keySet
      for (k <- commonKeys; s1p <- succ1(k); s2p <- succ2(k)) {
        productEdges += (((s1, s2), k, (s1p, s2p)))
        val next = (s1p, s2p)
        if (!seen(next)) {
          queue enqueue next
          seen += next
        }
      }
    }
    val targetStates2 = targetStates filter (seen(_))
    Automaton[GT.ELGT{type V = (P#V, P1#V); type EL = P#EL}](productEdges, init, targetStates2)
  }

  def initState_=(s: P#V): Automaton[P] = new Automaton(edges, s, targetStates)
  
  def targetStates_=(set: Set[P#V]): Automaton[P] = new Automaton(edges, initState, set)
  
  override def +(x: V, l: EL, y: V): Automaton[P] = new Automaton(super.+(x,l,y).adjacencyMap, initState, targetStates)
  override def +(x: (V, EL, V)): Automaton[P] = this + (x._1, x._2, x._3)
  override def +(x: V) : Automaton[P] = new Automaton(super.+(x).adjacencyMap, initState, targetStates)
  override def -(x: V, l: EL, y: V) : Automaton[P] = new Automaton(super.-(x,l,y).adjacencyMap, initState, targetStates)
  override def -(v: V) : Automaton[P] = { //TODO this method can return an automaton with an invalid init state, but that might happen (transient state) during some methods
    //assert(v != initState)
    new Automaton(super.-(v).adjacencyMap, initState, targetStates - v)
  }

  override def ++(moreNodes: Traversable[(V, EL, V)]): Automaton[P] = (this /: moreNodes)(_ + _)
  override def ++(graph: EdgeLabeledDiGraph[P]): Automaton[P] = {
    new Automaton(super.++(graph).adjacencyMap, initState, targetStates)
  }

  override def --(vs: Traversable[V]): Automaton[P] = (this /: vs)(_ - _)
  def remEdges(vs: Traversable[(V, EL, V)]): Automaton[P] = (this /: vs)((acc,e) => acc - (e._1,e._2,e._3))

  override def morph(map: PartialFunction[P#V, P#V]): Automaton[P] = {
    val changedGraph = super.morph(map)
    val changedInit = if (map isDefinedAt initState) map(initState) else initState
    val chandegTarget = targetStates map (s => if (map isDefinedAt s) map(s) else s)
    new Automaton[P](changedGraph.adjacencyMap, changedInit, chandegTarget)
  }

  def morphFull[Q <: GT.ELGT](nodes: P#V => Q#V, edges: P#EL => Q#EL): Automaton[Q] = {
    val newEdges = super.morphFull(nodes, edges, (x: Q#V) => ()).adjacencyMap
    val newInitState = nodes(initState)
    val newTargetStates = targetStates map nodes
    new Automaton[Q](newEdges, newInitState, newTargetStates)
  }

  /** Rename vertex "from" into vertex "to".
   * If "to" is already present then the two nodes are merged */
  def alpha(from: P#V, to: P#V): Automaton[P] = morph(Map(from -> to))
  
  /** Connect two automaton.
   * @param a the automaton to connect with
   * @param connections pairs of state belonging to the automata that should be one in the new automaton
   */
  def connect(a: Automaton[P], connections: Traversable[(P#V,P#V)], init: P#V = initState, target: Set[P#V] = targetStates): Automaton[P] = {
    //assert that the nodes of this and a are disjoint
    assert((vertices intersect a.vertices).isEmpty)
    val map = (Map.empty[P#V,P#V] /: connections){case (a, (n1, n2)) => a + (n2 -> n1)}
    val a2 = a morph map
    val res = this ++ a2
    //Logger("Graph", LogDebug, "connect "+ connections +"\n" + a.toGraphviz("a") + a2.toGraphviz("a2") + res.toGraphviz("res") )
    res
  }

  def replaceEdgeBy(e: (P#V, P#EL, P#V), a: Automaton[P], n1: P#V, n2: P#V): Automaton[P] = {
    val a2 = this.-(e._1, e._2, e._3)
    val res = a2.connect(a, List((e._1 -> n1),(e._3 -> n2)))
    //Logger("Graph", LogDebug, "replaceEdgeBy " + e + " adding\n" + a.toGraphviz("a") + " at " + n1 + ", " + n2 + "in\n" + this.toGraphviz("this") + "gives\n" + res.toGraphviz("res") )
    res
  }

  //TODO methods to manipulate automatons:
  // -path compaction (large block encoding)
  // -path expansion (refinement)
  // -more general morphism: to also change the labeling (abstracting code into a model)
  // -...

  /** Removes states that cannot be transitively reached from init (i.e. can never be reached) */
  def removeUnreachableStates: Automaton[P] = {
    val reachable = this.transitiveClosure((a,b) => a)(initState) + initState
    val unreachable = vertices -- reachable
    Logger("graph", LogDebug, "removeUnreachableStates: " + unreachable.mkString("",", ",""))
    this -- unreachable
  }

  def isTraceInitialized(t: Trace[P#V,P#EL]) = isTraceValid(t) && initState == t.start
  
  def isAcceptingTrace(t: Trace[P#V,P#EL]) = isTraceInitialized(t) && targetStates(t.stop)
  
  import scala.text.Document
  override def toGraphvizExplicit(name: String,
                                  prefix: String,
                                  inBody: Document,
                                  idPrefix: String,
                                  nodeProps: V => List[(String,String)],
                                  edgeProps: EL => List[(String,String)]): (Document, Map[V, String]) = {
    def nodeProps2(v: V) = {
      val p = nodeProps(v)
      if(v == initState) ("shape" , "octagon") :: p
      else if (targetStates(v)) ("shape" , "doubleoctagon") :: p
      else p
    }
    super.toGraphvizExplicit(name, prefix, inBody, idPrefix, nodeProps2, edgeProps)
  }

  def simplePathsAutomaton: Automaton[GT.ELGT{type V = P#V; type EL= List[P#EL]}] = {
    val paths = simplePaths
    val splittingNodes = targetStates.toSet + initState
    val allPaths = paths.flatMap(_.split(splittingNodes))
    val edges = allPaths.map( p => {
      val (s1, s2) = p.extremities
      (s1, p.labels, s2)
    })
    Automaton[GT.ELGT{type V = P#V; type EL= List[P#EL]}](edges, initState, targetStates)
  }

}

object Automaton extends {

  def apply[P <: GT.ELGT](edges: Traversable[(P#V,P#EL,P#V)], init: P#V, target: Traversable[P#V]): Automaton[P] = {
    val targetSet = target.toSet
    val map = Labeled.listToMap(targetSet + init, edges)
    new Automaton[P](map, init, targetSet)
  }

}
