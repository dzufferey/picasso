package picasso.transform

import picasso.ast._
import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.Variable
import picasso.graph._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

//TODO from AgentDefinition (a set of them) to a set of transition for DBP
//TODO from an initial state to a graph

abstract class DBPWrapper[A](val agents: Seq[AgentDefinition[A]], val init: Expression) extends DefDBP {
  type PC = A

  val transitions: Iterable[DBT]

  val initConf: DBCC

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

  //transition context: map: Map[ID, DBC#V]


  //TODO return a new map ?
  def makeStateFor(agt: AgentDefinition[PC], map: Map[ID, DBC#V], controlState: PC, params: Seq[(ID, Expression)]): (DBCN, DBCC) = {
    //complete the params: live values that are not defined ? (use Wildcard)
    val live = agt.liveVariables(controlState)
    val (defined, undef) = live.partition(id => params.exists(_._1 == id))
    val mainNode = DBCN(controlState)
    val graph1 = emptyConf + mainNode
    val (graph2, map2) = ((graph1, map) /: undef)( (graphAndMap, id) => {
      val ptsTo = unk
      val mapNew = graphAndMap._2 + (id -> ptsTo) 
      val graphNew = graphAndMap._1 + (mainNode, id.id, ptsTo)
      (graphNew, mapNew)
    })
    val (graph3, map3) = ((graph2, map2) /: defined)( (graphAndMap, id) => {
      val expr = params.find(_._1 == id).get._2
      val (pointed, graphExpr) = graphOfExpr(expr, graphAndMap._2)
      val mapNew = graphAndMap._2 + (id -> pointed) 
      val graphNew = graphAndMap._1 ++ graphExpr + (mainNode, id.id, pointed)
      (graphNew, mapNew)
    })
    (mainNode, graph3)
  }

  def initialConfiguration: DBCC = {
    //TODO look at init and create a DBCC
    //init is a list(tuple) of processID(args)
    sys.error("TODO")
  }

  //TODO interpreted fct: boolean + collection
  def isInterpreted(fct: String): Boolean = {
    sys.error("TODO")
  }

  def graphOfExpr(e: Expression, map: Map[ID, DBC#V]): (DBC#V, DBCC) = e match {
    case Any =>
      val node = DBCN_Any
      (node, emptyConf + node)
    case Value(literal) =>
      val node = DBCN(literal)
      (node, emptyConf + node)
    case NewChannel() =>
      val node = DBCN_Name
      (node, emptyConf + node)
    case Create(agt, args) =>
      val agtDef = agents.find(_.id == agt) match {
        case Some(aDef) => aDef
        case None => Logger.logAndThrow("AstToDBP", LogError, "agent '"+agt+"' no found")
      }
      makeStateFor(agtDef, map, agtDef.cfa.initState, agtDef.params zip args)
    case id @ ID(v) =>
      val node = map.getOrElse(id, unk)
      //TODO add id->node to the map and return the map ?
      (node, emptyConf + node)
    case Application(fct, args) =>
      if (isInterpreted(fct)) {
        Logger.logAndThrow("AstToDBP", LogError, "graphOfExpr does not deal with interpreted functions ("+fct+")")
      } else { //not interpreted (alg datatype)
        val refNode = DBCN_Case(fct)
        val sub = args.map(graphOfExpr(_,map)).zipWithIndex
        val graph = ((emptyConf + refNode) /: sub){case (acc, ((n,g),i)) => acc ++ g + (refNode, Variable(i.toString), n)} //TODO type ?
        (refNode, graph)
      }
    case Unit() =>
      val node = DBCN_Unit
      (node, emptyConf + node)
    case Tuple(args) => graphOfExpr(Application("Tuple", args), map)
  }

  //TODO boolean functions.
  //choose whether the result is true or false get the possible combinations of values that realize it
  //
  
  def makeTransition(a: PC, proc: Process, b: PC): Seq[DBT] = proc match {
    case Zero() =>
      val before = DBCN(a)
      val trs = makeTrans( proc.toString,
                           emptyConf + before, emptyConf,
                           Map.empty[DBC#V, DBC#V], Map.empty[DBC#V, DBC#V],
                           None )
      List(trs)
    case Skip() =>
      val before = DBCN(a)
      val after = DBCN(b)
      val trs = makeTrans( proc.toString,
                           emptyConf + before, emptyConf + after,
                           Map(before -> after), Map.empty[DBC#V, DBC#V],
                           None )
      List(trs)
    case Assert(e) => sys.error("TODO") //TODO boolean interpreted fct
    case Assume(e) => sys.error("TODO") //TODO boolean interpreted fct
    case Havoc(vars) => sys.error("TODO")
    case Block(lst) => sys.error("TODO")
    case Expr(expr) => sys.error("TODO")
    case Affect(variable, expr) => sys.error("TODO") //TODO isInterpreted ...
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
