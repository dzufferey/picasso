package picasso.transform

import picasso.ast._
import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, String => HString, Int => HInt, Wildcard => HWildcard, Binding => HBinding, _}
import picasso.graph._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}

//TODO from AgentDefinition (a set of them) to a set of transition for DBP
//TODO from an initial state to a graph

abstract class DBPWrapper[A](val agents: Seq[AgentDefinition[A]], val init: Expression) extends DefDBP {
  type PC = A

  lazy val transitions: Iterable[DBT] = makeTransitions(agents)

  lazy val initConf: DBCC = initialConfiguration(init)

  lazy val system = new DBP(transitions.toList)(confOrdering, ordering)

  //TODO LocalScope vs GlobalScope vs ClassScope ...
  //for the moment assumes only local

  //TODO (expr) split by type ? -> bool, string, actor, collection
  //The current solution is compilerPlugin/domains/ is somehow modular,
  //but not quite satisfying (too much happening behind the back).
  //also it requires some fancy ordering on the match cases in makeTransition.

  //what is the simplest way of translating all features in an unified way ?
  //expressions that are supposed to translate as graph: literal, variables(ref), patterns, alg-datatypes, ...
  //things that reflect change in the graphs: Assert/Assume, Havoc, Affect, Send, Receive

  //TODO all that stuff can move to DefDBP (if it is general enough)

  type Context = Map[ID, DBC#V] //when making a transition: keep track of the node created for an ID
  def emptyContext = Map.empty[ID, DBC#V]

  /**************************
  TODO this part should be modified to allows collection and boolean value to coexists (i.e. assert(isEmpty(bag)) )
  The trick before was to unroll, thus split the complec stuff in many simpler steps.
  However, for performance reason, we would like to keep the transitions as compact as possible.
  One reason it might be tricky, is that collection operation add inhibitory graphs ...
  boolean part: valuation (points to with T/F) -> result
  coolection part: something/nothing (points to _ as normal or inhibitory)
  TODO issue: which direction path goes ?
    how to express an object in a collection,
    the member of an obj in a collection ?
  This come from the fact that there is this implicit PC. with indirection this is not valid anymore (can be another node, not a PC)
  **************************/
  sealed abstract class PointsTo(id: ID)
  case class PtsToBoolValue(id: ID, value: Boolean) extends PointsTo(id)
  case class PtsToName(id: ID) extends PointsTo(id) //pts to a pi-calculus name
  case class PtsToCollection(id: ID) extends PointsTo(id) //the intermediary node used to model the collection
  case class PtsToSpecial(id: ID, what: String) extends PointsTo(id) //a specially named node
  case class PtsToWildCard(id: ID, tpe: HType) extends PointsTo(id) //keep the type to generate more credible aliasing (if we do aliasing)
  case class PtsToPath(id: ID, to: PointsTo) extends PointsTo(id)
  case class PtsToNot(id: ID, to: PointsTo) extends PointsTo(id) //for inhibitory stuff.
  //case class PtsToPC(id: ID, pc: PC) extends PointsTo(id) //the control state node (not really this, since this will be used for OO programming)
  //This actually is a set of constraints that represent some graph (set of graphs)
  //this is still rough and should combine easily with bool/collection reasoning
  //e.g. for boolean we should be able to interact with it as a Map[ID,Boolean]
  //We need something to encapsulate that thing to provide a simple view on it
  //It should support something like adding thing with a "boolean structure", i.e. some case splitting.
  //basic strategy it to accumulate a set of constraint and then at the end, compile them to transitions 

  //a "transition helper" for lack of better name is like a context on steroid:
  // -> does it need to be passed around ? yes or no ?
  // -> how to deal with the before/after/common part ? (PC, update, ...)
  // -> dependencies between constraints and case splitting ?
  // -> by-value vs by-reference (for wildcards)

  class TransitionHelper {

    //to remember the PCs
    protected val prePCs = scala.collection.mutable.HashSet[PC]()
    protected val postPCs = scala.collection.mutable.HashSet[PC]()
    protected val pairedPCs = scala.collection.mutable.Buffer[(PC,PC)]()

    protected var activePre: Option[PC] = None;
    protected var activePost: Option[PC] = None;

    //we want multiple PC to cohabit => allows for transition that involve multiple actors

    def addPCs(pre: PC, post: PC) = {       //for actors that make steps
      prePCs += pre
      postPCs += post
      pairedPCs += (pre -> post)
    }
    def creates(post: PC) = {               //for actors that are created
      postPCs += post
    }
    def dies(pre: PC) = {                   //for actors that finish
      prePCs += pre
    }
    def unchanged(pc: PC) = addPCs(pc, pc)  //for an actor that does not take a step
    
    def activePrePC(pc: PC) = {
      assert(prePCs(pc))
      activePre = Some(pc)
    }
    def activePostPC(pc: PC) = {
      assert(postPCs(pc))
      activePost = Some(pc)
    }
    def activePCs(pre: PC, post: PC) = {
      assert(prePCs(pre) && postPCs(post) && pairedPCs.contains(pre -> post))
      activePre = Some(pre)
      activePost = Some(post)
    }

    //use the active actor as reference process
    def addPreImplicit(constraints: PointsTo*) = {
      if (activePre.isEmpty) sys.error("forgot to specify the PC (addPreImplicit)")
      addPre(activePre.get, constraints:_*)
    }
    def addPostImplicit(constraints: PointsTo*) = {
      if (activePost.isEmpty) sys.error("forgot to specify the PC (addPostImplicit)")
      addPost(activePost.get, constraints:_*)
    }
    def addImplicit(preCstr: Seq[PointsTo], postCstr: Seq[PointsTo]) = {
      if (activePre.isEmpty || activePost.isEmpty) sys.error("forgot to specify the PCs (addImplicit)")
      val pre = activePre.get
      val post = activePost.get
      assert(pairedPCs.contains(pre -> post))
      add(pre, preCstr, post, postCstr)
    }
    
    def addPre(pc: PC, constraints: PointsTo*) = addPreAlternatives(Seq((pc, constraints.toSeq)))
    def addPost(pc: PC, constraints: PointsTo*) = addPostAlternatives(Seq((pc, constraints.toSeq)))
    def add(pre: PC, preCstr: Seq[PointsTo], post: PC, postCstr: Seq[PointsTo]) = addAlternatives((Seq(pre -> preCstr), Seq(post -> postCstr)))

    ////////////////////////////////
    //XXXXXXXXXXXXXXXXXXXXXXXXXXXX//
    ////////////////////////////////

    private sealed abstract class Constraints
    private case class Literal(pre: Boolean, pc: PC, cstr: PointsTo) extends Constraints
    private case class Conjunction(seq: Seq[Constraints]) extends Constraints
    private case class Disjunction(seq: Seq[Constraints]) extends Constraints

    private val constraints = scala.collection.mutable.Buffer[Constraints]()

    def addPreAlternatives(alternatives: Seq[(PC,Seq[PointsTo])]): Unit = {
      val parts = for ((pc, pts) <- alternatives) yield {
        Conjunction(pts.map(pt => Literal(true, pc, pt)))
      }
      constraints += Disjunction(parts)
    }
    
    def addPostAlternatives(alternatives: Seq[(PC,Seq[PointsTo])]): Unit = {
      val parts = for ((pc, pts) <- alternatives) yield {
        Conjunction(pts.map(pt => Literal(false, pc, pt)))
      }
      constraints += Disjunction(parts)
    }

    def addAlternatives(alternatives: (Seq[(PC,Seq[PointsTo])], Seq[(PC,Seq[PointsTo])])* ): Unit = {
      val parts = for ((pre, post) <- alternatives) yield {
        val preLits = for ((pc, pts) <- pre; pt <- pts) yield Literal(true, pc, pt)
        val postLits = for ((pc, pts) <- post; pt <- pts) yield Literal(false, pc, pt)
        Conjunction(preLits ++ postLits)
      }
      constraints += Disjunction(parts)
    }
    
    private def dnf(cstr: Constraints): Constraints = {
      def process(e: Constraints): Seq[Seq[Constraints]] = e match {
        case Conjunction(args) =>
          val subDnfs = args map process
          subDnfs.reduceLeft( (acc, disj) => disj.flatMap( conj => acc.map(conj2 => conj ++ conj2) ))
        case Disjunction(args) => args flatMap process
        case other => List(List(other))
      }
      Disjunction(process(cstr) map (x => Conjunction(x)))
    }

    private def compatibe(p1: Literal, p2: Literal): Boolean = {
      if (p1.pre ^ p2.pre) {
        false //p1 and p2 are not refering to the same time period
      } else {
        sys.error("TODO")
        /*
          case PtsToBoolValue(id, value)
          case PtsToName(id) //pts to a pi-calculus name
          case PtsToCollection(id) //the intermediary node used to model the collection
          case PtsToSpecial(id, what) extends PointsTo(id) //a specially named node
          case PtsToWildCard(id, tpe) //keep the type to generate more credible aliasing
          case PtsToPath(id, to)
          case PtsToNot(id, to) //for inhibitory stuff.
        */
      }
    }

    //TODO How to solve the constraints to generate a PartialDBT ?
    //The simplest thing should be to:
    //(1) put the constraints in DNF
    //(2) [optional] generate all the aliasing of nodes
    //(3) filter the one without solutions
    //(4) turn the constrains into graphs
    def compile: Seq[PartialDBT] = {
      //what happens with the pre/post thing ?
      //The literal indicate whether a constraint is about the pre or post state.
      
      //(1) DNF:
      //the "constrains" buffer is a big conjunction of disj of conj ...
      val disj = dnf(Conjunction(constraints))

      //(2) Aliasing: PointsTo that are of compatible types may be merged ?
      
      //(3) Filter the unsat
      
      //(4) Turn into PartialDBT
      
      sys.error("TODO")
    }
    
    ////////////////////////////////
    //XXXXXXXXXXXXXXXXXXXXXXXXXXXX//
    ////////////////////////////////

  }

  
  //TODO when an actor creates another actor of the same kind -> name clash!!
  def makeStateFor(agt: AgentDefinition[PC], map: Context, controlState: PC, params: Seq[(ID, Expression)]): Seq[(DBC#V, DBCC, Context)] = {
    //complete the params: live values that are not defined ? (use Wildcards or Any or case split ?)
    val live = agt.liveVariables(controlState)
    val (defined, undef) = live.partition(id => params.exists(_._1 == id))
    val mainNode = DBCN(controlState)
    val graph1 = emptyConf + mainNode
    val (graph2, map2) = ((graph1, map) /: undef)( (graphAndMap, id) => {
      val ptsTo = unkForID(id)
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
        case err => Logger.logAndThrow("DBPWrapper", LogWarning, "initialConfiguration expects Create, not "+err)
      }
      //first fetch the IDs -> assume those are channel
      val channels = processes.flatMap(_._2).flatMap{case id @ ID(_) => List(id) case _ => None}.toSet
      val context = channels.map(_ -> DBCN_Name).toMap[ID, DBC#V]
      val graphs = processes.map{ case (agt, args) =>
        val agtDef = agents.find(_.id == agt) match {
          case Some(aDef) => aDef
          case None => Logger.logAndThrow("DBPWrapper", LogError, "agent '"+agt+"' no found")
        }
        val newAgt = makeStateFor(agtDef, context, agtDef.cfa.initState, agtDef.params zip args)
        if (newAgt.size != 1) {
          Logger.logAndThrow("DBPWrapper", LogError, "initialConfiguration expects determinitic start configuration for "+agt+", got: " + newAgt)
        }
        newAgt.head._2
      }
      graphs.reduceLeft(_ ++ _)
    case err =>
      Logger.logAndThrow("DBPWrapper", LogWarning, "initialConfiguration expects a tuple, not "+err)
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
    case HClassType( _, _) | Channel() => true
    case HBool | HString | HInt | FiniteValues(_) => false
    case tpe @ (Function( _, _) | HWildcard | UnInterpreted(_) | TypeVariable(_) | Product(_)) => 
      Logger("DBPWrapper", LogWarning, "isReference("+id+") -> '"+tpe+"' ? returns true (defensive option)")
      true
  }

  def unkForID(id: ID) = if (id.id.tpe == Channel()) DBCN_Name else unk

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
      val node = context.getOrElse(id, unkForID(id))
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
          val node = unkForID(id)
          gA = gA + (nA, id.id, node)
          if (isReference(id)) { //keep a dangling node
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
    //TODO bug: this will always consume the node matched by the WC
    case Wildcard =>
      val node = unk
      (node, emptyConf + node, emptyContext)
    case Binding(id, pat) =>
      val (idNode, graph, map) = graphOfPattern(pat)
      (idNode, graph, map + (id -> idNode))
    case PatternTuple(lst) => graphOfPattern(Case("Tuple", lst))
    case _ => Logger.logAndThrow("DBPWrapper", LogError, "graphOfPattern??? " + e)
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
        case None => Logger.logAndThrow("DBPWrapper", LogError, "agent '"+agt+"' no found")
      }
      makeStateFor(agtDef, map, agtDef.cfa.initState, agtDef.params zip args)
    case id @ ID(v) =>
      val node = map.getOrElse(id, unkForID(id))
      Seq((node, emptyConf + node, map + (id -> node)))
    case ap @ Application(fct, args) =>
      if (isInterpreted(ap)) {
        Logger.logAndThrow("DBPWrapper", LogError, "graphOfExpr does not deal with interpreted functions ("+fct+")")
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
      Logger.logAndThrow("DBPWrapper", LogWarning, "graphForInterpretedExpr does only boolean for the moment, not " + e)
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
        val (g1, g2, forward, backward) = checkScope(agt, a, b, before, emptyConf + before, after, emptyConf + after, assign, Set.empty[ID])
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
        val (g1, g2, forward, backward) = checkScope(agt, a, b, before, emptyConf + before, after, emptyConf + after, assign, Set.empty[ID])
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
        Logger("DBPWrapper", LogWarning, "generating trivial transition for " + proc + " -> " + proc.toStringRaw)
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
      assert(dest.id.tpe == Channel())
      val startContext = emptyContext + (dest -> DBCN_Name)
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
      assert(src.id.tpe == Channel())
      val startContext = emptyContext + (src -> DBCN_Name)
      val (patN, patG, patC) = graphOfPattern(pat)
      val graphBe = patG + (before, src.id, startContext(src)) + (patN, msgDest, startContext(src))
      val graphAf = emptyConf + after ++ patC.toList.map{ case (id, n) => (after, id.id, n)}
      val (g1, g2, forward, backward) = checkScope(agt, a, b, before, graphBe, after, graphAf, startContext, patC.keySet)
      Seq(makeTrans( proc.toString, g1, g2, forward, backward, None))

    case other =>
      Logger.logAndThrow("DBPWrapper", LogError, "not supported " + other + " -> " + other.toStringRaw)
  }

  def makeTransitions(agt: AgentDefinition[PC]): Seq[DBT] = {
    val rawTrs = agt.cfa.edges.flatMap{ case (a,proc,b) =>
      val trs = makeTransition(agt, a, proc, b)
      Logger("DBPWrapper", LogDebug,
             "transition for " + (a,proc,b) + " ->\n" +
             trs.map(t => Misc.docToString(t.toGraphviz(""))).mkString("","\n","\n\n"))
      trs
    }.toSeq
    rawTrs map checkTransition
  }

  def makeTransitions(agts: Seq[AgentDefinition[PC]]): Seq[DBT] = {
    agts flatMap makeTransitions
  }

}
