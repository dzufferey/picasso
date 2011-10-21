package picasso.transform

import picasso.ast._
import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, String => HString, Int => HInt, Wildcard => HWildcard, Binding => HBinding, _}
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

  //TODO should have an inermediate language of graph constraints ?
  //this can then be used to generate the real transition graph.
  //this could also take care of the aliasing problems (generates the transition with and without aliases)
  //...

  //TODO when an actor creates another actor of the same kind -> name clash!!
  def makeStateFor(agt: AgentDefinition[PC], map: Context, controlState: PC, params: Seq[(ID, Expression)]): Seq[(DBC#V, DBCC, Context)] = {
    //complete the params: live values that are not defined ? (use Wildcards or Any or case split ?)
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
    def processArgs(args: Seq[(ID, Expression)], acc: DBCC, context: Context): Seq[(DBCC, Context)] = args.headOption match {
      case Some((id,x)) => graphOfExpr(x, context).flatMap{ case (n,g,c) =>
        val acc2 = acc ++ g + (mainNode, id.id, n)
        processArgs(args.tail, acc2, c)
      }
      case None => Seq(acc -> context)
    }
    val graphsAndContexts = processArgs(params.filter(p => defined(p._1)), graph2, map2)
    graphsAndContexts.map{case (graph, context) => (mainNode, graph, context)}
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

  def isReference(id: ID): Boolean = id.id.tpe match {
    case HClassType( _, _) => true
    case HBool | HString | HInt | FiniteValues(_) => false
    case tpe @ (Function( _, _) | HWildcard | UnInterpreted(_)) => 
      Logger("AstToDBP", LogWarning, "isReference("+id+") -> '"+tpe+"' ? returns true (defensive option)")
      true
  }

  def graphForNonInterpretedExpr(e: Expression, map: Context): Seq[(DBC#V, DBCC, Context)] = e match {
    case Any =>
      val node = DBCN_Any
      Seq((node, emptyConf + node, map))
    case Value(literal) =>
      val node = DBCN(literal)
      Seq((node, emptyConf + node, map))
    case NewChannel() =>
      val node = DBCN_Name
      Seq((node, emptyConf + node, map))
    case Create(agt, args) =>
      val agtDef = agents.find(_.id == agt) match {
        case Some(aDef) => aDef
        case None => Logger.logAndThrow("AstToDBP", LogError, "agent '"+agt+"' no found")
      }
      makeStateFor(agtDef, map, agtDef.cfa.initState, agtDef.params zip args)
    case id @ ID(v) =>
      val node = map.getOrElse(id, unk)
      Seq((node, emptyConf + node, map + (id -> node)))
    case Application(fct, args) =>
      if (isInterpreted(fct)) {
        Logger.logAndThrow("AstToDBP", LogError, "graphOfExpr does not deal with interpreted functions ("+fct+")")
      } else { //not interpreted (alg datatype)
        val refNode = DBCN_Case(fct)
        def processArgs(args: List[Expression], idx: Int, acc: DBCC, context: Context): Seq[(DBCC, Context)] = args match {
          case x::xs => graphOfExpr(x, context).flatMap{ case (n,g,c) =>
            val acc2 = acc ++ g + (refNode, Variable(idx.toString)/*TODO tpe*/, n)
            processArgs(xs, idx+1, acc2, c)
          }
          case Nil => Seq(acc -> context)
        }
        val graphsAndContexts = processArgs(args, 0, emptyConf + refNode, map)
        graphsAndContexts.map{case (graph, context) => (refNode, graph, context)}
      }
    case Unit() =>
      val node = DBCN_Unit
      Seq((node, emptyConf + node, map))
    case Tuple(args) => graphOfExpr(Application("Tuple", args), map)
  }

  def graphForInterpretedExpr(e: Expression, map: Context): Seq[(DBC#V, DBCC, Context)] = {
    if (BooleanFunctions.isBooleanInterpreted(e)) {
      val trueAssigns = BooleanFunctions.assigns(true, e) map boolAssignToNode
      val falseAssigns = BooleanFunctions.assigns(false, e) map boolAssignToNode
      //TODO check map is compatible with the assigns
      val resultTrue = trueAssigns.map( assign => {
        val node = DBCN(Bool(true))
        (node, emptyConf + node, map ++ assign)
      })
      val resultFalse = falseAssigns.map( assign => {
        val node = DBCN(Bool(false))
        (node, emptyConf + node, map ++ assign)
      })
      resultTrue ++ resultFalse
    } else {
      Logger.logAndThrow("AstToDBP", LogWarning, "graphForInterpretedExpr does only boolean for the moment, not " + e)
    }
  }
  
  def graphOfExpr(e: Expression, map: Context): Seq[(DBC#V, DBCC, Context)] = e match {
    case Application(fct, _) =>
      if (isInterpreted(fct)) graphForInterpretedExpr(e, map)
      else graphForNonInterpretedExpr(e, map)
    case _ => graphOfExpr(e, map)
  }

  //returns: new, live, dying
  def compareScopes(agt: AgentDefinition[PC], a: PC, b: PC): (Set[ID], Set[ID], Set[ID]) = {
    val atA = agt.liveVariables(a)
    val atB = agt.liveVariables(b)
    (atB diff atA, atA intersect atB, atA diff atB)
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
      //actually not that trivial -> some values may go out of scope, so they should be removed
      val (coming, staying, dying) = compareScopes(agt, a, b)
      assert(coming.isEmpty)
      val before = DBCN(a)
      val after = DBCN(b)
      val stayingNodes = staying.map(_ -> unk).toMap
      val dyingNodes = dying.map(_ -> unk).toMap
      val danglingNodes = dyingNodes.filterKeys(isReference(_))
      val beforeGraph = emptyConf + before ++ (stayingNodes ++ dyingNodes).map{case (id,n) => (before, id.id, n)}
      val afterGraph = (emptyConf /: danglingNodes.values)(_+_) + after ++ stayingNodes.map{case (id,n) => (after, id.id, n)}
      val mapForward = Map(before -> after)
      val mapBackward = Map.empty[DBC#V, DBC#V] ++ (stayingNodes ++ danglingNodes).map(n => (n._2, n._2))
      val trs = makeTrans( proc.toString, beforeGraph, afterGraph,
                           mapForward, mapBackward, None)
      List(trs)
    
    case Assert(e) =>
      //TODO change to use graphForInterpretedExpr
      assert(BooleanFunctions.isBooleanInterpreted(e))
      val emp = Seq[(ID, Expression)]()
      val trueAssigns = BooleanFunctions.assigns(true, e) map boolAssignToNode
      val trueTrs = for(assign <- trueAssigns;
                        ((node1, graph1, context1), (node2, graph2, context2)) <-
                          makeStateFor(agt, assign, a, emp) zip makeStateFor(agt, assign, b, emp)) yield {
        val (kept, news) = context1.keys.partition(k => context2 contains k)
        assert(news.isEmpty)
        val (defined, undefs) = kept.partition(k => isUnk(context2(k)))
        val mapForward = Map(node1 -> node2) ++ defined.map(k => (context1(k), context2(k)))
        val mapBackward = Map.empty[DBC#V,DBC#V] ++ undefs.map(k => (context2(k), context1(k)))
        makeTrans( proc.toString, graph1, graph2, mapForward, mapBackward, None)
      }
      val falseAssigns = BooleanFunctions.assigns(false, e) map boolAssignToNode
      val falseTrs = for(assign <- falseAssigns;
                        (node1, graph1, context1) <- makeStateFor(agt, assign, a, emp)) yield {
        val error = DBCN_Error
        val mapForward = Map(node1 -> error)
        makeTrans( proc.toString, graph1, emptyConf + error, mapForward, Map.empty[DBC#V,DBC#V], None)
      }
      trueTrs ++ falseTrs
    
    case Assume(e) => //assumes are more relaxed than assert (they don't fail on false, just block)
      //TODO change to use graphForInterpretedExpr
      assert(BooleanFunctions.isBooleanInterpreted(e))
      val emp = Seq[(ID, Expression)]()
      val trueAssigns = BooleanFunctions.assigns(true, e) map boolAssignToNode
      val trueTrs = for(assign <- trueAssigns;
                        ((node1, graph1, context1), (node2, graph2, context2)) <-
                          makeStateFor(agt, assign, a, emp) zip makeStateFor(agt, assign, b, emp)) yield {
        val (kept, news) = context1.keys.partition(k => context2 contains k)
        assert(news.isEmpty)
        val (defined, undefs) = kept.partition(k => isUnk(context2(k)))
        val mapForward = Map(node1 -> node2) ++ defined.map(k => (context1(k), context2(k)))
        val mapBackward = Map.empty[DBC#V,DBC#V] ++ undefs.map(k => (context2(k), context1(k)))
        makeTrans( proc.toString, graph1, graph2, mapForward, mapBackward, None)
      }
      trueTrs
    
    case Havoc(vars) =>
      sys.error("TODO Havoc")
    
    case Block(lst) =>
      //TODO make sure it is not too tricky to translate (scope of temporary variables)
      //the dimplest way is to introduce tmp variables
      sys.error("TODO Block")
      
    case Expr(expr) => 
      if (hasSideEffect(expr)) {
        for ((_, graph, context) <- graphOfExpr(expr, emptyContext)) yield {
          val before = DBCN(a)
          val after = DBCN(b)
          val beforeScope = context.filterKeys(k => agt.liveVariables(a)(k))
          val afterScope = context.filterKeys(k => agt.liveVariables(b)(k))
          val danglingNodes = beforeScope.filterKeys(k => !afterScope.contains(k) && isReference(k)) //dead values can be discarded
          assert(afterScope.keySet subsetOf beforeScope.keySet)//no element that comes out of nowhere
          val beforeGraph = emptyConf + before ++ beforeScope.toList.map{ case (k,v) => (before, k.id, v)}
          val afterGraph = (graph /: danglingNodes.values)(_+_) + after ++ afterScope.toList.map{ case (k,v) => (after, k.id, v)}
          val (defined, undefs) = beforeScope.filterKeys(k => afterScope.contains(k) || danglingNodes.contains(k)).partition{case (k,v) => isUnk(v)}
          val mapForward = Map(before -> after) ++  defined.map(k => (k._2, k._2))
          val mapBackward = Map.empty[DBC#V,DBC#V] ++ undefs.map(k => (k._2, k._2))
          makeTrans( proc.toString, beforeGraph, afterGraph, mapForward, mapBackward, None)
        }
      } else {
        Logger("AstToDBP", LogWarning, "generating trivial transition for " + proc + " -> " + proc.toStringRaw)
        makeTransition(agt, a, Skip(), b)
      }
      
    case Affect(variable, expr) =>
      val cases = graphOfExpr(expr, emptyContext)
      val before = DBCN(a)
      val after = DBCN(b)
      val (coming, staying, dying) = compareScopes(agt, a, b)
      for ((node, graph, context) <- cases) yield {
        //TODO before: all read variables + the old value of variables (if live)
        //TODO after: after -> node (+ things that are still live)
        sys.error("TODO: ...")
      }

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
