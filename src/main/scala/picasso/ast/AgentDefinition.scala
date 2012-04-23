package picasso.ast

import scala.collection.immutable.Set
import scala.collection.immutable.Map
import scala.text.Document
import picasso.graph._
import picasso.utils.Misc

//TODO rather than Process on the edges, should have some guarded command language
/** An agent ...
 *  TODO params should be a list of pattern ?
 *  @param id the name of the agent kind
 *  @param params the parameters for the agent creation
 *  @param transitions transitions
 *  @param init the initial location
 *  @param target the exit locations
 */
class AgentDefinition[PC](val id: String, val params: List[ID], val cfa: Automaton[GT.ELGT{type V = PC; type EL = Process}]){

  def this(id: String, params: List[ID], transition: Map[PC,Map[Process,Set[PC]]], init: PC, target: Set[PC]) = 
    this(id, params, new Automaton[GT.ELGT{type V = PC; type EL = Process}](transition, init, target))


  def morphFull[PC2](nodes: PC => PC2, edges: Process => Process): AgentDefinition[PC2] = {
    new AgentDefinition(id, params, cfa.morphFull[GT.ELGT{type V = PC2; type EL = Process}](nodes, edges))
  }
  
  def toGraphviz(name: String, prefix: String, idPrefix: String): Document = {
    import scala.text.Document._
    val inBody =
      if ((name startsWith "cluster_") && (prefix == "subgraph"))
        text("label = " + Misc.quote(id + params.mkString("(",",",")")) + ";")
      else
        empty
    cfa.toGraphvizFull(name, prefix, inBody, idPrefix)._1
  }
  
  override def toString = "agent: " + id + params.mkString("(",",",")") + "\n" + cfa

  //TODO checks if the agent is "unrolled", i.e. have only simple (easy to translate) expression on the edges.

  //TODO have a scope of live variables (so we can detect a read from unk/any)
  lazy val liveVariables: Map[PC, Set[ID]] = {
    val read = readMap
    val written = writeMap
    assert(written.keySet == read.keySet)
    read.map{ case (k,v) => (k, v intersect written(k))}
  }

  //defaultValue: at the initState, the argument are written!
  lazy val writeMap: Map[PC, Set[ID]] = {
    def default(s: PC) = if (s == cfa.initState) params.toSet
                         else Set.empty[ID]
    cfa.aiFixpoint( ((written: Set[ID], p: Process) => written ++ p.writtenIDs),//TODO only correct if there are no blocks
                    ((a: Set[ID], b: Set[ID]) => a ++ b),
                    ((a: Set[ID], b: Set[ID]) => b subsetOf a),
                    default,
                    true)
  }

  lazy val readMap: Map[PC, Set[ID]] = 
    cfa.aiFixpointBackward( ((read: Set[ID], p: Process) => read -- p.writtenIDs ++ p.readIDs),//TODO only correct if there are no blocks
                            ((a: Set[ID], b: Set[ID]) => a ++ b),
                            ((a: Set[ID], b: Set[ID]) => b subsetOf a),
                            (_ => Set.empty[ID]) )

  //what about the read from Any ?
  //(1) do a case split (more expensive but provide increase precision)
  //(2) propagate the Any (not really precise since x!=x might become true)
  //remark: the case split is needed for send/receive

  //TODO send by value or send by name ? (depends on the type: lit by val, obj by name)

  //TODO be more aggressive:
  // -variable that are not live can be thrown away
  // -variable that are always Any can be removed (and constant propagation)

  protected def neverEnabled(p: Process): Boolean = p match {
    case Assume(Value(Bool(false))) => true
    case _ => false
  }

  //phase 1: remove the edges that are never enabled
  protected def compactNeverEnabled = {
    val ne = cfa.edges filter (e => neverEnabled(e._2))
    val cfa2 = cfa remEdges ne
    val reachableNodes = cfa2.nodesReachableFrom(cfa2.initState) + cfa2.initState
    val unreachableNodes = cfa2.vertices -- reachableNodes
    val cfa3 = cfa2 -- unreachableNodes
    new AgentDefinition(id, params, cfa3)
  }

  /** Transition where nothing occurs afterward (exit or error) */
  protected def finalTransition(p: Process): Boolean = p match {
    case Assert(Value(Bool(false))) | Zero() => true
    //TODO what about assert(Any) ?
    case _ => false
  }
  
  //phase 2: remove the things after the final transitions
  protected def compactFinalTransition = {
    val fe = cfa.edges filter (e => finalTransition(e._2))
    //first remove those edges, then remove the unreachable nodes
    val cfa2 = cfa remEdges fe
    val reachableNodes = cfa2.nodesReachableFrom(cfa2.initState) + cfa2.initState
    val unreachableNodes = cfa2.vertices -- reachableNodes
    val cfa3 = cfa2 -- unreachableNodes
    //then put the edges back (only if the start node is in the graph)
    val edgesToAdd = fe.filter(e => reachableNodes(e._1))
    val feTargets = (Set.empty[PC] /: edgesToAdd)( (acc, e) => acc + e._1 + e._3 ).filter(cfa.targetStates(_))
    val cfa4 = cfa3 ++ edgesToAdd
    val newTargets = cfa4.targetStates ++ feTargets
    val cfa5 = new Automaton(cfa4.adjacencyMap, cfa4.initState, newTargets)
    new AgentDefinition(id, params, cfa5)
  }

  protected def canSkip(p: Process): Boolean = p match {
    case Skip() | Expr(Any) | Expr(Value(_)) |
         Assert(Value(Bool(true))) | Assume(Value(Bool(true))) => true
    //TODO what about assume(Any) ?
    case _ => false
  }
  
  //phase 3: compact the edges that can be skipped (merge nodes together)
  protected def compactSkip = {
    //TODO 
    //if canSkip, do not impact SCC,
    //no other outgoing edge in src or not other ingoing edge in dest
    val sccs = cfa.SCC
    val mapToSCC = Map[PC,Int](( sccs.zipWithIndex.flatMap( p => p._1.map((_, p._2))) ):_*)
    val rev = cfa.reverse
    def canMerge(edge: (PC, Process, PC)): Boolean = {
      val scc1 = mapToSCC.getOrElse(edge._1, -2) + 1 //so that there is no 0 index
      val scc2 = mapToSCC.getOrElse(edge._3, -2) + 1
      //Console.println("edge: " + edge)
      //Console.println("canSkip: " + canSkip(edge._2))
      //Console.println("scc1 = " + scc1 + ", scc2 = " + scc2)
      //Console.println("out = " + cfa(edge._1).size + ", inc = " + rev(edge._3).size)
      canSkip(edge._2) &&
      (scc1 == scc2 || scc1 * scc2 < 0) &&
      (cfa(edge._1).size == 1 || rev(edge._3).size == 1)
    }
    //merging is removing edge + merging nodes (morph)
    val edgesToRemove = cfa.edges filter canMerge
    val cfa2 = cfa remEdges edgesToRemove
    val toMergeEdges = edgesToRemove.flatMap{ case (a,_,b) => List((a,b),(b,a))}
    val toMergeSCC = DiGraph[GT.ULGT{type V = PC}](toMergeEdges).SCC
    val toMergeMorphism = Map[PC,PC](toMergeSCC.flatMap(scc => scc.toList.map(_ -> scc.head)):_*)
    val cfa3 = cfa2.morph(toMergeMorphism)
    new AgentDefinition(id, params, cfa3)
  }
  
  /** remove useless edge to get a smaller agent.
   *  do it in a fixpoint. */
  def compact: AgentDefinition[PC] = {
    val compacted = compactNeverEnabled.compactFinalTransition.compactSkip
    if (compacted.cfa.vertices.size < cfa.vertices.size ||
        compacted.cfa.edges.size < cfa.edges.size )
      compacted.compact
    else
      compacted
  }


}
