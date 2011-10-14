package picasso.transform

import picasso.ast._
import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.Variable
import picasso.graph._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

//TODO from AgentDefinition (a set of them) to a set of transition for DBP
//TODO from an initial state to a graph

/* TODO
 */

abstract class DBPWrapper[A](agents: Seq[AgentDefinition[A]], init: Expression) extends DefDBP {
  type PC = A

  import scala.collection.mutable.Buffer

  val transitions = Buffer.empty[DBCT]

  var initConf: DBCC = null //TODO null is bad!!

}

trait AstToDBP[A] {
  self: DBPWrapper[A] =>

  //import self._

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

  //TODO (expr) split by type ? -> bool, string, actor, collection
  //The current solution is compilerPlugin/domains/ is somehow modular,
  //but not quite satisfying (too much happening behind the back).
  //also it requires some fancy ordering on the match cases in makeTransition.

  //what is the simplest way of translating all features in an unified way ?
  //expressions that are supposed to translate as graph: literal, variables(ref), patterns, alg-datatypes, ...
  //things that reflect change in the graphs: Assert/Assume, Havoc, Affect, Send, Receive

  //TODO creation might be somehow ...
  def graphOfExpr(e: Expression, map: Map[ID, DBC#V]): (DBC#V, DBCC) = e match {
    case Any => sys.error("TODO")
    case Value(Bool(b)) => sys.error("TODO")
    case Value(StringVal(str)) => sys.error("TODO")
    case Value(other) => sys.error("TODO")
    case NewChannel() => sys.error("TODO")
    case Create(agt, args) => sys.error("TODO")
    //TODO interpreted fct: boolean + collection
    case Application(fct, args) => sys.error("TODO") //not an interpreted fct -> alg data type
    case id @ ID(v) => sys.error("TODO")
    case Unit() => sys.error("TODO")
    case Tuple(args) => sys.error("TODO")
  }
  
  def makeTransition(a: PC, proc: Process, b: PC): Seq[DBT] = proc match {
    case Zero() => sys.error("TODO")
    case Skip() => sys.error("TODO")
    case Assert(e) => sys.error("TODO")
    case Assume(e) => sys.error("TODO")
    case Havoc(vars) => sys.error("TODO")
    case Block(lst) => sys.error("TODO")
    case Expr(expr) => sys.error("TODO")
    case Affect(variable, expr) => sys.error("TODO")
    case Send(dest, content) => sys.error("TODO")
    case Receive(src, pat) => sys.error("TODO")
  }

  def makeTransitions(agts: AgentDefinition[PC]): Seq[DBT] = {
    sys.error("TODO")
  }

  def makeTransitions(agts: Seq[AgentDefinition[PC]]): Seq[DBT] = {
    agts flatMap makeTransitions
  }

}
