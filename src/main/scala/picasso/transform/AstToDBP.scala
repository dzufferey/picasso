package picasso.transform

import picasso.ast._
import picasso.model.dbp._

//TODO from AgentDefinition (a set of them) to a set of transition for DBP
//TODO from an initial state to a graph

/* TODO
 * translation of patterns
 * translation of expression: boolean, stringLit
 * translation of send, receive
 * translation of create, new-channel, assert, assume, havoc
 * translation of set operations
 */
class AstToDBP[PC]() {

  //TODO type for the returned DBP
  //this can be copy pasted from compilerPlugin/backend/AuxDefinitions.scala
  //now the issue is that putting everything as nested classes limits the scope of what is visible and what we can do.
  //or put this at the top level, but then ...
  //or wrap it using mixin

  //check that the processes on the edges are things that are easy to translate.
  //otherwise it might need to unrolling
  def easyToTransform(agt: AgentDefinition[PC]): Boolean = {
    sys.error("TODO")
  }

  //def makeTransitions(agts: Seq[AgentDefinition[PC]]): ... {
  //}

}
