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

  lazy val transitions: Iterable[DBT] = makeTransitions(agents)

  lazy val initConf: DBCC = initialConfiguration(init)

  //TODO LocalScope vs GlobalScope vs ClassScope ...
  //for the moment assumes only local

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

  //TODO a way to automatically handle the scope issues

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

  def initialConfiguration(init: Expression): DBCC = init match {
    case Tuple(lst) =>
      val processes = lst map {
        case Create(name, args) => (name, args)
        case err => Logger.logAndThrow("AstToDBP", LogWarning, "initialConfiguration expects Create, not "+err)
      }
      //first fetch the IDs -> assume those are channel
      val channels = processes.flatMap(_._2).flatMap{case id @ ID(_) => List(id) case _ => None}.toSet
      val context = channels.map(_ -> DBCN_Name).toMap[ID, DBC#V]
      val graphs = processes.map{ case (agt, args) =>
        val agtDef = agents.find(_.id == agt) match {
          case Some(aDef) => aDef
          case None => Logger.logAndThrow("AstToDBP", LogError, "agent '"+agt+"' no found")
        }
        val newAgt = makeStateFor(agtDef, context, agtDef.cfa.initState, agtDef.params zip args)
        if (newAgt.size != 1) {
          Logger.logAndThrow("AstToDBP", LogWarning, "initialConfiguration expects determinitic start configuration")
        }
        newAgt.head._2
      }
      graphs.reduceLeft(_ ++ _)
    case err =>
      Logger.logAndThrow("AstToDBP", LogWarning, "initialConfiguration expects a tuple, not "+err)
  }

  def boolAssignToNode(assign: Map[ID, Boolean]): Context = {
    for ((id,value) <- assign) yield (id,DBCN(Bool(value)))
  }

  //interpreted fct: boolean + collection
  def isInterpreted(e: Expression): Boolean = {
    //TODO more: collections
    //TODO only one level (bool)
    BooleanFunctions.isBooleanInterpreted(e)
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

  ////////////////////////////
  // take care of the scope //
  ////////////////////////////
  
  /** Assumes that the nodes in context are read.
   *  For nodes that don't die and that are not assigned, carry over the read value.
   */
  def checkScope( agt: AgentDefinition[PC], a: PC, b: PC,
                  nA: DBC#V, _gA: DBCC, nB: DBC#V, _gB: DBCC,
                  context: Context, assigned: Set[ID]
                ): (DBCC, DBCC, Map[DBC#V, DBC#V], Map[DBC#V, DBC#V]) = {
    //as variables that we can modify
    var gA = _gA
    var gB = _gB
    var forward = Map(nA -> nB)
    var backward = Map.empty[DBC#V, DBC#V]
    //first put all the read variables
    for ((id,n) <- context) gA = gA + (nA, id.id, n)
    //
    val (coming, staying, dying) = compareScopes(agt, a, b)
    //for coming nodes: nothing special, just check that they are assigned
    assert(coming subsetOf assigned)
    //for dying nodes: checks they are in A and not in B, + keep dangling node for references
    for (id <- dying) {
      val node = context.getOrElse(id, unk)
      gA = gA + (nA, id.id, node)
      if (isReference(id)) { //keep a dangling node
        gB = gB + node
      } else if (gB.edgesWith(node).isEmpty) { //remove the node if there are no edges from/to it
        gB = gB - node
      } //else pointed by/points to some otherthing, better keep it.
    }
    //for the staying nodes: checks they are in both. If their values change, check if danglingNodes must be kept.
    for (id <- staying) {
      if (context contains id) {//accessed
        val node = context(id)
        if (assigned contains id) {//gets a new value
          if (isReference(id)) { //keep a dangling node
            gB = gB + node
          } else if (gB.edgesWith(node).isEmpty) { //remove the node if there are no edges from/to it
            gB = gB - node
          }
        } else {
          gB = gB + (nB, id.id, node)
        }
      } else {//not accessed
        if (assigned contains id) {//gets a new value
          if (isReference(id)) { //keep a dangling node
            val node = unk
            gA = gA + (nA, id.id, node)
            gB = gB + node
          }
        }
      }
    }
    for (n <- gA.vertices intersect gB.vertices) {//TODO check that this is address equality, not pointer equality.
      if (isUnk(n)) backward = backward + (n -> n)
      else forward = forward + (n -> n)
    }
    (gA, gB, forward, backward)
  }


  ////////////////////////////
  ////////////////////////////
  ////////////////////////////

  /** The precondition graph that a pattern matches + mapping of bindings'id to graph node.
   * @returns (main node, graph, binding \mapsto node) */
  def graphOfPattern(e: Pattern): (DBC#V, DBCC, Context) = e match {
    case Case(name, lst) =>
      val refNode = DBCN_Case(name)
      val sub = (lst map graphOfPattern).zipWithIndex
      val (graph, map) = ((emptyConf + refNode, Map.empty[ID,DBC#V]) /: sub){
        case ((g1,m1), ((n,g2,m2),i)) => (g1 ++ g2 + (refNode, Variable(i.toString), n), m1 ++ m2) //TODO Variable type
      }
      (refNode, graph, map)
    case PatternLit(literal) =>
      val node = DBCN(literal)
      (node, emptyConf + node, emptyContext)
    case Wildcard =>
      val node = unk
      (node, emptyConf + node, emptyContext)
    case Binding(id, pat) =>
      val (idNode, graph, map) = graphOfPattern(pat)
      (idNode, graph, map + (id -> idNode))
    case PatternTuple(lst) => graphOfPattern(Case("Tuple", lst))
    case _ => Logger.logAndThrow("AstToDBP", LogError, "graphOfPattern??? " + e)
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
    case ap @ Application(fct, args) =>
      if (isInterpreted(ap)) {
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
  
  def graphOfExpr(e: Expression, map: Context): Seq[(DBC#V, DBCC, Context)] = {
    if (isInterpreted(e)) graphForInterpretedExpr(e, map)
    else graphForNonInterpretedExpr(e, map)
  }

  //returns: new, live, dying
  def compareScopes(agt: AgentDefinition[PC], a: PC, b: PC): (Set[ID], Set[ID], Set[ID]) = {
    val atA = agt.liveVariables(a)
    val atB = agt.liveVariables(b)
    (atB diff atA, atA intersect atB, atA diff atB)
  }

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
      val (beforeG, afterG, forward, backward) = checkScope(agt, a, b, before, emptyConf + before, after, emptyConf + after, emptyContext, Set.empty[ID])
      val trs = makeTrans( proc.toString, beforeG, afterG, forward, backward, None)
      List(trs)
    
    case Assert(e) =>
      //TODO change to use graphOfExpr
      assert(BooleanFunctions.isBooleanInterpreted(e))
      val before = DBCN(a)
      val after = DBCN(b)
      val trueAssigns = BooleanFunctions.assigns(true, e) map boolAssignToNode
      val trueTrs = for(assign <- trueAssigns) yield {
        val (g1, g2, forward, backward) = checkScope(agt, a, b, before, emptyConf + before, after, emptyConf + after, emptyContext, Set.empty[ID])
        makeTrans( proc.toString, g1, g2, forward, backward, None)
      }
      val falseAssigns = BooleanFunctions.assigns(false, e) map boolAssignToNode
      val falseTrs = for(assign <- falseAssigns;
                        (node1, graph1, context1) <- makeStateFor(agt, assign, a, Seq[(ID, Expression)]())) yield {
        val error = DBCN_Error
        val mapForward = Map(node1 -> error)
        makeTrans( proc.toString, graph1, emptyConf + error, mapForward, Map.empty[DBC#V,DBC#V], None)
      }
      trueTrs ++ falseTrs
    
    case Assume(e) => //assumes are more relaxed than assert (they don't fail on false, just block)
      //TODO change to use graphOfExpr
      assert(BooleanFunctions.isBooleanInterpreted(e))
      val before = DBCN(a)
      val after = DBCN(b)
      val trueAssigns = BooleanFunctions.assigns(true, e) map boolAssignToNode
      val trueTrs = for(assign <- trueAssigns) yield {
        val (g1, g2, forward, backward) = checkScope(agt, a, b, before, emptyConf + before, after, emptyConf + after, emptyContext, Set.empty[ID])
        makeTrans( proc.toString, g1, g2, forward, backward, None)
      }
      trueTrs
    
    case Havoc(vars) =>//TODO case split of Any ?
      sys.error("TODO Havoc")
    
    case Block(lst) =>
      //TODO make sure it is not too tricky to translate (scope of temporary variables)
      //the simplest way is to introduce tmp variables
      sys.error("TODO Block")
      
    case Expr(expr) => 
      if (hasSideEffect(expr)) {
        for ((_, graph, context) <- graphOfExpr(expr, emptyContext)) yield {
          val before = DBCN(a)
          val after = DBCN(b)
          val graphBe = emptyConf + before
          val graphAf = graph + after
          val (g1, g2, forward, backward) = checkScope(agt, a, b, before, graphBe, after, graphAf, context, Set.empty[ID])
          makeTrans( proc.toString, g1, g2, forward, backward, None)
        }
      } else {
        Logger("AstToDBP", LogWarning, "generating trivial transition for " + proc + " -> " + proc.toStringRaw)
        makeTransition(agt, a, Skip(), b)
      }
      
    case Affect(id, expr) => //TODO for the moment assumes that everything has a local scope.
      if (agt.liveVariables(b)(id)) { //need to remember id
        val before = DBCN(a)
        val after = DBCN(b)
        val cases = graphOfExpr(expr, emptyContext)
        for ((node, graph, context) <- cases) yield {
          val graphBe = emptyConf + before
          val graphAf = graph + (after, id.id, node)
          val (g1, g2, forward, backward) = checkScope(agt, a, b, before, graphBe, after, graphAf, context, Set(id))
          makeTrans( proc.toString, g1, g2, forward, backward, None)
        }
      } else { //otherwise like an expr
        makeTransition(agt, a, Expr(expr), b)
      }

    case Send(dest @ ID(_), content) =>
      val (coming, staying, dying) = compareScopes(agt, a, b)
      val before = DBCN(a)
      val after = DBCN(b)
      val startContext = emptyContext + (dest -> unk)
      for ((contentN, contentG, contentC) <- graphOfExpr(content, startContext)) yield {
        val graphBe = emptyConf + (before, dest.id, startContext(dest))
        val graphAf = contentG + after + (contentN, msgDest, startContext(dest))
        val (g1, g2, forward, backward) = checkScope(agt, a, b, before, graphBe, after, graphAf, contentC, Set.empty[ID])
        makeTrans( proc.toString, g1, g2, forward, backward, None)
      }

    case Receive(src @ ID(_), pat) =>
      val (coming, staying, dying) = compareScopes(agt, a, b)
      val before = DBCN(a)
      val after = DBCN(b)
      val startContext = emptyContext + (src -> unk)
      val (patN, patG, patC) = graphOfPattern(pat)
      val graphBe = patG + (before, src.id, startContext(src)) + (patN, msgDest, startContext(src))
      val graphAf = emptyConf + after ++ patC.toList.map{ case (id, n) => (after, id.id, n)}
      val (g1, g2, forward, backward) = checkScope(agt, a, b, before, graphBe, after, graphAf, startContext, patC.keySet)
      Seq(makeTrans( proc.toString, g1, g2, forward, backward, None))

    case other =>
      Logger.logAndThrow("AstToDBP", LogError, "not supported " + other + " -> " + other.toStringRaw)
  }

  def makeTransitions(agt: AgentDefinition[PC]): Seq[DBT] = {
    val rawTrs =agt.cfa.edges.flatMap{case (a,proc,b) => makeTransition(agt, a, proc, b)}.toSeq
    rawTrs map checkTransition
  }

  def makeTransitions(agts: Seq[AgentDefinition[PC]]): Seq[DBT] = {
    agts flatMap makeTransitions
  }

}