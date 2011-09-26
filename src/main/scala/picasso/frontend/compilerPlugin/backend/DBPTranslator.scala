package picasso.frontend.compilerPlugin.backend

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin._
import scala.tools.nsc._
import picasso.ast.{Ident => PIdent, Value => PValue, Process => PProcess, Block => PBlock, _}
import picasso.utils.Namer
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, String => HString, Wildcard => HWildcard, Binding => HBinding, _}

/** The last transformation step: going from PiCode to DBP */
trait DBPTranslator {
  self: AnalysisUniverse =>

  import global._

  //TODO this would not work with aliasing (subgraph cannot merge two unks to match one node)

  //TODO all this is now BUGGY
  // -make distinction between values and references (values can be consummed) this might be usefull to reduce the depth of the transition graph
  // -what happens is getter setter for OTHER classes are used to reduce the number of transition (i.e. more than one this). note that this may already happens now ...
  // -also needs a better way to handle case classes/objects
  // -assert & error state

  //would it make sense to generate a special "error state that is reached by assert that are false and so on ..."

  //Configuration

  //returns ref + table
  //TODO initial values of the variables and or ctor call
  def initStatic(c: PClass): (DBC#V, DBC#V) = {
    //assumes the ctor is empty ?
    val newRef = DBCN(c.id)
    val newDispatch = DBCN(c.dispatchTable.agent.cfa.initState)
    //val ctor = c.methods.find(_._1.isPrimaryConstructor).get._2
    (newRef, newDispatch)
  }

  def initialConfiguration: DBCC = {
    val statics = PClasses.staticObjects
    val main = PClasses.mainClass.get
    val woMain = statics filterNot (_ == main)
    val mainMethod = main.methods.find(p => isMainMethod(p._1)).get._2
    val thisAndReturn = mainMethod.agent.params.map(_.id)
    val returnNode = DBCN("finished")
    val otherEdges = (woMain map initStatic) map {case (ref,tbl) => (tbl, thisVar, ref)}
    val (mainRef,mainTbl) = initStatic(main)
    val mainNode = DBCN(mainMethod.agent.cfa.initState)
    val argsNode = defaultCollectionNode
    makeConf(otherEdges) +
            ((mainTbl,thisVar,mainRef)) +
            ((mainNode,thisAndReturn(0),mainRef)) +
            ((mainNode,thisAndReturn(1),returnNode)) +
            ((mainNode,thisAndReturn(2),argsNode))
  }

  /** Deal with access to variable that are either in the class, local, or global.
   *  @param methodExec the node from where id is accessed
   *  @param obj the object that contains the class variables 
   *  @param id the variable to access
   *  @param ptsTo the node pointed by id
   */
  def accessID(methodExec: DBC#V, obj: DBC#V, id: ID, ptsTo: Option[DBC#V]): (DBC#V, List[(DBC#V,DBC#EL,DBC#V)]) = id.accessMode match {
    case LocalScope =>
      val node = ptsTo getOrElse unk
      node -> List((methodExec,id.id,node))
    case ClassScope =>
      val node = ptsTo getOrElse unk
      node -> List((methodExec,thisVar,obj), (obj,id.id,node))
    case GlobalScope => 
      //only create a new node if necessary (checks if given node can be used)
      val node1 = ptsTo getOrElse DBCN(id.id.toString)
      val node = if (node1.state.toString == id.id.toString) node1 else DBCN(id.id.toString)
      (node -> Nil)
  }
  def accessID(methodExec: DBC#V, obj: DBC#V, id: ID, ptsTo: DBC#V): List[(DBC#V,DBC#EL,DBC#V)] = {
    val (ptsTo2, edges) = accessID(methodExec, obj, id, Some(ptsTo))
    assert(ptsTo2 == ptsTo, ptsTo + " == " + ptsTo2)
    edges
  }

  /** returns the possible initconfiguration of the method.
   *  Assumes that all the IDs in args are references.
   */
  def initStates(m: MethodExecutor, args: List[Expression]): (PC, List[(ID,ID)]) = {
    //Console.println("initStates with " + args + " -> " + m.agent.cfa)
    val loc = m.agent.cfa.initState
    val paired = m.agent.params.zip(args).flatMap{case (id1, id2 @ ID(_)) => List(id1->id2); case _ => Nil}
    (loc, paired.filter(p => p._1 == thisChannel || testLive(m.liveAt,loc,p._1)))
  }

  /** generate the post graph of pattern as expr + mapping of bindings'id to graph node.
   * @returns (main node, graph, binding \mapsto node)
   */
   //if everything was be made correctly that would be unnecessary
  def graphOfExpr(e: Expression, map: Map[ID, DBC#V]): (DBC#V, DBCC) = e match {
    case Application(fct, args) => 
      val refNode = DBCN(fct)
      val sub = args.map(graphOfExpr(_,map)).zipWithIndex
      val graph = ((emptyConf + refNode) /: sub){case (acc, ((n,g),i)) => acc ++ g + (refNode, Variable(i.toString), n)} //TODO type
      (refNode, graph)
    case id @ ID(v) =>
      //remark: static references should not be considered as live (as implmented now), we can use that => can never be in the map
      val node = if (map contains id) {
        //assert(id.accessMode == LocalScope) accessMode is not relevant here.
        map(id) 
      } else { //reference to case object id
        //TODO this is an hugly hack
        DBCN(v.name.substring(0, v.name.indexOf('#')))
      }
      (node, emptyConf + node)
    case PValue(Bool(b)) =>
      val node = DBCN(b.toString)
      (node, emptyConf + node)
    case PValue(StringVal(str)) =>
      val node = DBCN("\"" + str + "\"")
      (node, emptyConf + node)
    case Any =>
      val node = DBCN("Any")
      (node, emptyConf + node)
    case Tuple(args) => graphOfExpr(Application("Tuple", args), map)
    case _ => Logger.logAndThrow("Plugin", LogError, "graphOfExpr ??? " + e)
  }

  /** The precondition graph that a pattern matches + mapping of bindings'id to graph node.
   * @returns (main node, graph, binding \mapsto node)
   */
  def graphOfPattern(e: Pattern): (DBC#V, DBCC, Map[ID, DBC#V]) = e match {
    case Case(name, lst) =>
      val refNode = DBCN(name)
      val sub = (lst map graphOfPattern).zipWithIndex
      val (graph, map) = ((emptyConf + refNode, Map.empty[ID,DBC#V]) /: sub){
        case ((g1,m1), ((n,g2,m2),i)) => (g1 ++ g2 + (refNode, Variable(i.toString), n), m1 ++ m2) //TODO Variable type
      }
      (refNode, graph, map)
    case PatternLit(Bool(b)) =>
      val node = DBCN(b.toString)
      (node, emptyConf + node, Map.empty[ID, DBC#V])
    case PatternLit(StringVal(str)) =>
      val node = DBCN("\"" + str + "\"")
      (node, emptyConf + node, Map.empty[ID, DBC#V])
    case Binding(id, pat) =>
      val (idNode, graph, map) = graphOfPattern(pat)
      (idNode, graph, Map[ID, DBC#V](id -> idNode))
    case PatternTuple(lst) => graphOfPattern(Case("Tuple", lst))
    case Wildcard =>
      val node = unk
      (node, emptyConf + node, Map.empty[ID, DBC#V])
    case _ => Logger.logAndThrow("Plugin", LogError, "graphOfPattern??? " + e)
  }

  /** if b is a target state or '0', then no successor node. */
  def isFinalState(agt: AgentDefinition[PC], pc: PC) = {
    val finalState = (pc == "0") || (agt.cfa.targetStates(pc))
    if (finalState) assert(agt.cfa(pc).isEmpty)
    finalState
  }

  /** Test if some ID is live at some point. Take into account the scope of id */
  def testLive(liveAt: Map[PC,Set[ID]], loc: PC, id: ID) =
    !(id.accessMode == LocalScope) || liveAt(loc)(id)

  def makeAffect( a: PC,//from
                  b: PC,//to
                  p: Affect,//the statement
                  liveAt: Map[PC,Set[ID]],
                  thisNode: DBC#V,
                  n1: DBC#V,//= DBCN(a)
                  n2: DBC#V,//= DBCN(b)
                  lhsPartial: DBCC,
                  mapIDlhs: Map[ID, DBC#V],
                  rhsPartial: DBCC,
                  mapForward: Map[DBC#V,DBC#V],
                  mapBackward: Map[DBC#V,DBC#V]
                ): (String, DBCC, DBCC, Map[DBC#V,DBC#V], Map[DBC#V,DBC#V], Option[DBCC]) = {
    //(1) get what is live, and what should die
    val variable = p.id //only thing that gets written
    val varLiveBefore = testLive(liveAt,a,variable)
    val allRead = readIDs(p) filter canDoSomethingWith //possible that variable is part of allRead
    val (staying, dying) = allRead.partition(testLive(liveAt,b,_))
    //(2) adapt the lhs
    val addToKillIDs = (dying ++ (if (varLiveBefore) List(variable) else Nil)) -- mapIDlhs.keys
    val addToKill = addToKillIDs.map(id => (id, unk))
    val g1 = lhsPartial ++ addToKill.flatMap{case (id, node) => accessID(n1,thisNode,id,node)}
    //(3) adapt the rhs
    //Console.println("staying = " + staying.mkString)
    //Console.println("dying= " + dying.mkString)
    //Console.println("mapIDlhs= " + mapIDlhs.keySet.mkString)
    val alsoAfterIDs = staying & mapIDlhs.keySet
    val preMapFull = mapIDlhs ++ addToKill
    val alsoAfter = alsoAfterIDs map (id => (id, preMapFull(id)))
    val danglingNodes = preMapFull.values //filter values and keep only reference
    val rhsPartial2 = rhsPartial ++ alsoAfter.flatMap{ case (id, node) => accessID(n2,thisNode,id,node) }
    val g2 = (rhsPartial2 /: danglingNodes)(_ + _)
    //(4) mappings
    val mapping = mapForward + (n1 -> n2)
    val mappingBack = mapBackward ++ preMapFull.map{ case (_,n) => (n,n) }
    val transitionTitle = Namer(p.toString) 
    //(5) check that thisNode is in neither or both
    val hasThisNode = g1.vertices(thisNode) || g2.vertices(thisNode)
    val g1p1 = if (hasThisNode) g1 + (n1,thisVar,thisNode) else g1
    val g2p1 = if (hasThisNode) g2 + (n2,thisVar,thisNode) else g2
    //(6) most of the transitions assumes that p.id is live after, but that is not always the case.
    val g1p2 = g1p1
    val g2p2 = if (testLive(liveAt,b,variable)) g2p1 else {
      assert(variable.accessMode == LocalScope) //this handle only local (class + global are assumed to be always live)
      val fromN2= g2p1.adjacencyMap.get(n2).flatMap(_.get(variable.id))
      val edges = fromN2.map(set => set.toList.map(x => (n2, variable.id, x))).getOrElse(Nil)
      assert(edges.size <= 1)
      Logger("Plugin", LogDebug, "makeAffect: " + variable + " is not live at " + b + " removing: " + edges.mkString)
      (g2p1 /: edges){case (g,(a,b,c)) => g - (a,b,c) }
    }
    //TODO assertion and sanity checks!
    (transitionTitle, g1p2, g2p2, mapping, mappingBack + (thisNode -> thisNode), None)
  }

  //for some weird compiler "bug" it is better to put the extractors first, otherwise it might not even call them ?

  def commonEdgeToGraph: PartialFunction[(PClass, PC, PProcess, PC, Map[PC, Set[ID]]), Seq[PartialDBT]] = {
    case (clazz, a, p @ Assert(e), b, liveAt) => {
      val thisNode = unk
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      val simpleMapping = Map(n1 -> n2)
      val simpleG1 = emptyConf + n1
      val simpleG2 = emptyConf + n2
      val trs: List[(DBCC,DBCC,Map[DBC#V,DBC#V],Map[DBC#V,DBC#V])] = e match {
        case PValue(Bool(true)) => List((simpleG1, simpleG2, simpleMapping, Map.empty[DBC#V,DBC#V]))
        case PValue(Bool(false)) =>
          val errNode = errorState
          List((simpleG1, emptyConf + errNode, Map(n1 -> errNode), Map.empty[DBC#V,DBC#V]))
        case id @ ID(v) if v.tpe == HBool =>
          val valueNodes = List((matchTrueAny, n2), (matchFalseAny, errorState))
          valueNodes map { case(n,n2) =>
            val g1 = makeConf(accessID(n1,thisNode,id,n))
            val g2 =
              if (testLive(liveAt, b, id)) makeConf(accessID(n2,thisNode,id,n))
              else if (g1.vertices contains thisNode) makeConf(List((n2,thisVar,thisNode))) + n
              else emptyConf + n2 + n
            (g1, g2, Map(n1 -> n2), Map(thisNode -> thisNode, n -> n))
          }
        case _ =>
          Logger("Plugin", LogWarning, "Assert that matters bt what to do ?: " + p)
          List((simpleG1, simpleG2, simpleMapping, Map.empty[DBC#V,DBC#V]))
      }
      trs.map{ case (g1, g2, mapping, mappingBack) => (p.toString, g1, g2, mapping, mappingBack, None) }
    }
    
    case (clazz, a, p @ Assume(e), b, liveAt) => {
      val thisNode = unk
      val collectionNode = unk
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      val mapping = Map(n1 -> n2)
      val (g1, g2, mappingBack, forbidden) = e match {
        case SetIsEmpty(set @ ID(_)) =>
          val g1 = emptyConf + n1
          val g2 = emptyConf + n2
          val forbidden = makeConf(accessID(n1,thisNode,set,collectionNode)) + (collectionNode, collectionMember(set.id), unk)
          (g1,g2,Map.empty[DBC#V, DBC#V],Some(forbidden))

        case id @ ID(v) if v.tpe == HBool =>
          assert(testLive(liveAt,a,id))
          val valueNode = matchTrueAny
          val g1 = makeConf(accessID(n1,thisNode,id,valueNode))
          val g2 = if (testLive(liveAt,b,id)) makeConf(accessID(n1,thisNode,id,valueNode)) else emptyConf + n2 + valueNode
          val g2p = if (g1.vertices(thisNode)) g2 + (n1,thisVar,thisNode) else g2
          (g1,g2p,Map(valueNode -> valueNode),None)

        case Application("!", List(id @ ID(_))) =>
          assert(testLive(liveAt,a,id))
          val valueNode = matchFalseAny
          val g1 = makeConf(accessID(n1,thisNode,id,valueNode))
          val g2 = if (testLive(liveAt,b,id)) makeConf(accessID(n1,thisNode,id,valueNode)) else emptyConf + n2 + valueNode
          val g2p = if (g1.vertices(thisNode)) g2 + (n1,thisVar,thisNode) else g2
          (g1,g2p,Map(valueNode -> valueNode),None)
        
        case other => 
          Logger("Plugin", LogWarning, "Assume contains " + other + " -> don't know what to do")
          val g1 = emptyConf + n1
          val g2 = emptyConf + n2
          (g1,g2,Map.empty[DBC#V, DBC#V],None)
      }
      List((p.toString, g1, g2, Map(n1 -> n2), mappingBack, forbidden))
    }

    case (clazz, a, af @ Affect(id @ ID(_), NewChannel()), b, liveAt) => {
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      val n3 = fresh
      val thisNode = unk
      val g1 = emptyConf + n1
      val g2 = makeConf(accessID(n2,thisNode,id,n3))
      val tr = makeAffect(a, b, af, liveAt,
                          thisNode, n1, n2,
                          g1, Map.empty[ID,DBC#V], g2,
                          Map.empty[DBC#V, DBC#V], Map.empty[DBC#V, DBC#V])
      List(tr)
    }
    
    //dispatch table -> new methodExec
    case (clazz, a, p @  Expr(Create(id, args @ (ID(thisRef) :: _))), b, liveAt) => {
      //loosing the 'this' reference
      val candidate = clazz.methods.find(p => p._2.id == id).get._2
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      val thisNode = unk
      val argsSet = args.toSet //remove duplicates
      val refs = argsSet.flatMap{
        case v @ ID(`thisRef`) => List(v -> thisNode)
        case v @ ID(_) => List(v -> unk)
        case Any => Nil //Any should happens for only unsupported stuff
        case other => Logger.logAndThrow("Plugin", LogError, "args not ID: " + other)
      }.toSeq
      val g1 = makeConf(refs.flatMap{case (a,b) => accessID(n1,thisNode,a,b)})
      val liveAfter = refs.filter(p => testLive(liveAt,b,p._1))
      val (loc, mappings) = initStates(candidate, args)
      val locNode = DBCN(loc)
      val bEdges = liveAfter.flatMap{case (id,n) => accessID(n2,thisNode,id,n)}
      def nodeOf(id: ID) = refs.find(_._1 == id).get._2
      val locEdges = mappings.flatMap{case (id1,id2) => accessID(locNode,thisNode,id1,nodeOf(id2))}
      val nodesLost = refs.map(_._2)//this is an overapprox
      val g2 = (makeConf(bEdges ++ locEdges) /: nodesLost)(_ + _)
      val mapping = Map(n1 -> n2)
      val mappingBack = Map(nodesLost.map(n => (n,n)):_*) ++ (bEdges ++ locEdges).map(e => (e._3, e._3)) + (thisNode -> thisNode)
      List((p.toString, g1, g2, mapping, mappingBack, None))
    }
    
    //(within method) new objects 
    case (_, a, af @ Affect(id @ ID(_), Create(clazz, NewChannel() :: Nil)), b, liveAt) => {
      val candidate = PClasses.find(p => idOfSymbol(p._1) == clazz).get._2
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      val thisNode = unk
      val newRef = DBCN(candidate.id)
      val newDispatch = DBCN(candidate.dispatchTable.agent.cfa.initState)
      //TODO it seems that not all variables are taken: inherited are not here ??
      val variables = candidate.instanceVariables.map(IDOfSymbol).filter(canDoSomethingWith)
      //Console.println("XXXXXXXXXXXXXXXXXXXXXXXXX")
      //Console.println(clazz + " instanceVariables: " + candidate.instanceVariables)
      //Console.println(clazz + " variables: " + variables)
      //Console.println("XXXXXXXXXXXXXXXXXXXXXXXXX")
      val variablesEdges = variables.flatMap(id => accessID(newDispatch, newRef, id, DBCN(Any.toString)))
      val g1 = (makeConf(Nil) + n1)
      val g2 = makeConf(accessID(n2,thisNode,id,newRef) ++ variablesEdges) + (newDispatch,thisVar,newRef)
      val tr = makeAffect(a, b, af, liveAt,
                          thisNode, n1, n2,
                          g1, Map.empty[ID,DBC#V], g2,
                          Map.empty[DBC#V, DBC#V], Map.empty[DBC#V, DBC#V])
      List(tr)
    }
    
    //case af @ Affect(id @ ID(_), label @ ID(_)) if (isReference(id) || isReference(label)) => 
    case (clazz, a, af @ Affect(id @ ID(_), label @ ID(_)), b, liveAt) if (canDoSomethingWith(id) || canDoSomethingWith(label)) => {
      assert(testLive(liveAt,a,label))
      //assert(isReference(id) && isReference(label))
      assert(canDoSomethingWith(id) && canDoSomethingWith(label))
      val thisNode = unk
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      val (newValue, g1Base) = accessID(n1,thisNode,label,None)
      val g1 = makeConf(g1Base) + n1 + newValue 
      val g2 = makeConf(accessID(n2,thisNode,id,newValue)) 
      val tr = makeAffect(a, b, af, liveAt,
                          thisNode, n1, n2,
                          g1, Map(label -> newValue), g2,
                          Map.empty[DBC#V, DBC#V], Map(newValue -> newValue))
      List(tr)
    }
    
    case (clazz, a, p @ Affect(variable, PValue(lit)), b, liveAt) => {
      val stringNode = nodeForLiteral(lit)
      val thisNode = unk
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      val g1 = emptyConf + n1
      val g2 = emptyConf ++ accessID(n2,thisNode,variable,stringNode)
      val tr = makeAffect(a, b, p, liveAt,
                          thisNode, n1, n2,
                          g1, Map.empty[ID, DBC#V], g2,
                          Map.empty[DBC#V, DBC#V], Map.empty[DBC#V, DBC#V])
      List(tr)
    }

    //TODO is it possible to keep Any (depends on how the boolean operations are done later)
    case (clazz, a, Affect(variable, Any), b, liveAt) if (variable.id.tpe == HString) => {
      transitionForEdge(clazz, a, Affect(variable, PValue(StringVal("Any"))), b, liveAt)
    }

    case (clazz, a, PBlock(_), b, liveAt) => Logger.logAndThrow("Plugin", LogError, "cannot generate a transition out of a PBlock")
  }

  def transitionForEdge(clazz: PClass, a: PC, proc: PProcess, b: PC, liveAt: Map[PC, Set[ID]]): Seq[PartialDBT] = {
    val args = (clazz, a, proc, b, liveAt)
    val candidates = operations.filter(_.edgeToGraph.isDefinedAt(args))
    if (candidates.size > 1) {
      Logger("Plugin", LogWarning, "transitionForEdge: multiple matches for " + proc + " -> " + candidates.map(_.name).mkString("",", ",""))
      candidates(0).edgeToGraph(args)
    } else if (candidates.size == 1) {
      Logger("Plugin", LogDebug, "transitionForEdge: " + proc + " using " + candidates(0).name)
      candidates(0).edgeToGraph(args)
    } else if (commonEdgeToGraph isDefinedAt args) {
      Logger("Plugin", LogDebug, "transitionForEdge: " + proc)
      commonEdgeToGraph(args)
    } else {
      Logger("Plugin", LogWarning, "generating trivial transition for " + proc + " -> " + proc.toStringRaw)
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      val g1 = emptyConf + n1
      val g2 = emptyConf + n2
      List((proc.toString, g1, g2, Map(n1 -> n2), Map.empty[DBC#V, DBC#V], None))
    }
  }

  def transitionForAgent(clazz: PClass, agt: AgentDefinition[PC], liveAt: Map[PC, Set[ID]]): Iterable[DBT] = {
    def makeTr(a: PC, proc: PProcess, b: PC) = {
      val trs = transitionForEdge(clazz, a, proc, b, liveAt)
      val readyToPack = if (agt.cfa.targetStates(b)) {
        //if b is final remove it from the transitions (graph and maps)
        trs map { case (title, g1, g2, mapForward, mapBackward, forbidden) =>
          val bStates = g2.vertices.filter(_.state == DBCS[PC](b))
          //Console.println("g2 -> " + g2.vertices)
          //Console.println("b("+b+") -> " + bStates)
          assert(!bStates.isEmpty)
          val g2p = (g2 /: bStates)(_ - _)
          val mapForwardp = mapForward.filterNot{case (_,b) => bStates(b)}
          val mapBackwardp = mapBackward -- bStates
          (title, g1, g2p, mapForwardp, mapBackwardp, forbidden)
        }
      } else {
        trs
      }
      readyToPack map {case (a,b,c,d,e,f) =>  makeTrans(a,b,c,d,e,f)}
    }
    agt.cfa.edges.flatMap{case (a,proc,b) => makeTr(a, proc, b)}
  }

  def transitionForClass(c: PClass): Iterable[DBT] = {
    val methods = (c.methods.values map (exec => transitionForAgent(c, exec.agent, exec.liveAt))).reduceLeft(_ ++ _)
    methods ++ transitionForAgent(c, c.dispatchTable.agent, c.dispatchTable.liveAt)
  }

  def transitions: List[DBT] =
    PClasses.values.map(transitionForClass).flatten.toList


  def makeProcess: (DBCC, DBP) = {
    val init = initialConfiguration
    val sys = new DBP(transitions)(confOrdering, ordering)
    (init, sys)
  }

}
