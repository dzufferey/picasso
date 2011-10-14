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
                    default)
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

}
