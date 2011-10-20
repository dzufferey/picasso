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

  type Context = Map[ID, DBC#V] //when making a transition: keep track of the node created for an ID
  def emptyContext = Map.empty[ID, DBC#V]


  //TODO when an actor creates another actor of the same kind -> name clash!!
  def makeStateFor(agt: AgentDefinition[PC], map: Context, controlState: PC, params: Seq[(ID, Expression)]): (DBC#V, DBCC, Context) = {
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
      val (pointed, graphExpr, mapExpr) = graphOfExpr(expr, graphAndMap._2)
      //TODO check that the context and the expr are compatible.
      val mapNew = mapExpr + (id -> pointed) 
      val graphNew = graphAndMap._1 ++ graphExpr + (mainNode, id.id, pointed)
      (graphNew, mapNew)
    })
    (mainNode, graph3, map3)
  }

  def boolAssignToNode(assign: Map[ID, Boolean]): Context = {
    for ((id,value) <- assign) yield (id,DBCN(Bool(value)))
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

  def hasSideEffect(e: Expression): Boolean = e match {
    case NewChannel() | Create(_, _) => true
    case Application(fct, args) => args exists hasSideEffect //TODO or interpreted fct with side effect
    case Tuple(args) => args exists hasSideEffect
    case _ => false
  }

  def graphOfExpr(e: Expression, map: Context): (DBC#V, DBCC, Context) = e match {
    case Any =>
      val node = DBCN_Any
      (node, emptyConf + node, map)
    case Value(literal) =>
      val node = DBCN(literal)
      (node, emptyConf + node, map)
    case NewChannel() =>
      val node = DBCN_Name
      (node, emptyConf + node, map)
    case Create(agt, args) =>
      val agtDef = agents.find(_.id == agt) match {
        case Some(aDef) => aDef
        case None => Logger.logAndThrow("AstToDBP", LogError, "agent '"+agt+"' no found")
      }
      makeStateFor(agtDef, map, agtDef.cfa.initState, agtDef.params zip args)
    case id @ ID(v) =>
      val node = map.getOrElse(id, unk)
      (node, emptyConf + node, map + (id -> node))
    case Application(fct, args) =>
      if (isInterpreted(fct)) {
        Logger.logAndThrow("AstToDBP", LogError, "graphOfExpr does not deal with interpreted functions ("+fct+")")
      } else { //not interpreted (alg datatype)
        val refNode = DBCN_Case(fct)
        val sub = Array.ofDim[(DBC#V, DBCC, Int)](args.size)
        val newContext = (map /: args.zipWithIndex){ case (acc, (a,i)) => 
          val (n,g,c) = graphOfExpr(a, acc)
          sub(i) = (n,g,i)
          c
        }
        val graph = ((emptyConf + refNode) /: sub){ case (acc, (n,g,i)) => acc ++ g + (refNode, Variable(i.toString), n)} //TODO type ?
        (refNode, graph, newContext)
      }
    case Unit() =>
      val node = DBCN_Unit
      (node, emptyConf + node, map)
    case Tuple(args) => graphOfExpr(Application("Tuple", args), map)
  }

  //TODO boolean functions.
  //choose whether the result is true or false get the possible combinations of values that realize it
  //
  
  def makeTransition(agt: AgentDefinition[PC], a: PC, proc: Process, b: PC): Seq[DBT] = proc match {
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
    case Assert(e) =>
      assert(BooleanFunctions.isBooleanInterpreted(e))
      val trueAssigns = BooleanFunctions.assigns(true, e) map boolAssignToNode
      val trueTrs = for(assign <- trueAssigns) yield {
        val (node1, graph1, context1) = makeStateFor(agt, assign, a, Seq[(ID, Expression)]())
        val (node2, graph2, context2) = makeStateFor(agt, assign, b, Seq[(ID, Expression)]())
        val (kept, news) = context1.keys.partition(k => context2 contains k)
        assert(news.isEmpty)
        val (defined, undefs) = kept.partition(k => isUnk(context2(k)))
        val mapForward = Map(node1 -> node2) ++ defined.map(k => (context1(k), context2(k)))
        val mapBackward = Map.empty[DBC#V,DBC#V] ++ undefs.map(k => (context2(k), context1(k)))
        makeTrans( proc.toString, graph1, graph2, mapForward, mapBackward, None)
      }
      val falseAssigns = BooleanFunctions.assigns(false, e) map boolAssignToNode
      val falseTrs = for(assign <- falseAssigns) yield {
        val (node1, graph1, context1) = makeStateFor(agt, assign, a, Seq[(ID, Expression)]())
        val error = DBCN_Error
        val mapForward = Map(node1 -> error)
        makeTrans( proc.toString, graph1, emptyConf + error, mapForward, Map.empty[DBC#V,DBC#V], None)
      }
      trueTrs ++ falseTrs
    case Assume(e) => //assumes are more relaxed than assert (they don't fail on false, just block)
      assert(BooleanFunctions.isBooleanInterpreted(e))
      val trueAssigns = BooleanFunctions.assigns(true, e) map boolAssignToNode
      val trueTrs = for(assign <- trueAssigns) yield {
        val (node1, graph1, context1) = makeStateFor(agt, assign, a, Seq[(ID, Expression)]())
        val (node2, graph2, context2) = makeStateFor(agt, assign, b, Seq[(ID, Expression)]())
        val (kept, news) = context1.keys.partition(k => context2 contains k)
        assert(news.isEmpty)
        val (defined, undefs) = kept.partition(k => isUnk(context2(k)))
        val mapForward = Map(node1 -> node2) ++ defined.map(k => (context1(k), context2(k)))
        val mapBackward = Map.empty[DBC#V,DBC#V] ++ undefs.map(k => (context2(k), context1(k)))
        makeTrans( proc.toString, graph1, graph2, mapForward, mapBackward, None)
      }
      trueTrs
    case Havoc(vars) =>
      sys.error("TODO")
    case Block(lst) =>
      //TODO make sure it is not too tricky to translate (scope of temporary variables)
      //the dimplest way is to introduce tmp variables
      sys.error("TODO")
    case Expr(expr) => 
      if (hasSideEffect(expr)) {
        val (_, graph, context) = graphOfExpr(expr, emptyContext)
        val before = DBCN(a)
        val after = DBCN(b)
        val beforeScope = context.filterKeys(k => agt.liveVariables(a)(k))
        val afterScope = context.filterKeys(k => agt.liveVariables(b)(k))
        val danglingNodes = beforeScope.filterKeys(k => !afterScope.contains(k)) //TODO k is a reference, not a value (dead values can be discarded) -> look at the type of k
        assert(afterScope.keySet subsetOf beforeScope.keySet)//no element that comes out of nowhere
        val beforeGraph = emptyConf + before ++ beforeScope.toList.map{ case (k,v) => (before, k.id, v)}
        val afterGraph = (graph /: danglingNodes.values)(_+_) + after ++ afterScope.toList.map{ case (k,v) => (after, k.id, v)}
        sys.error("TODO connect the things in scope")
      } else {
        Logger("AstToDBP", LogWarning, "generating trivial transition for " + proc + " -> " + proc.toStringRaw)
        makeTransition(agt, a, Skip(), b)
      }
    case Affect(variable, expr) => sys.error("TODO") //TODO isInterpreted ...
    case Send(dest, content) => sys.error("TODO")
    case Receive(src, pat) => sys.error("TODO")
  }

  def makeTransitions(agt: AgentDefinition[PC]): Seq[DBT] = {
    sys.error("TODO")
  }

  def makeTransitions(agts: Seq[AgentDefinition[PC]]): Seq[DBT] = {
    agts flatMap makeTransitions
  }

}
