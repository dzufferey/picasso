package picasso.frontend.compilerPlugin.backend

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer}
import picasso.frontend.compilerPlugin._
import picasso.ast.{Ident => PIdent, Process => PProcess, Block => PBlock, _}
import picasso.math.hol.{Wildcard => HWildcard, _}
import picasso.graph.{GT, DiGraph, Automaton, Labeled}
import scala.tools.nsc._
import scala.collection.mutable.HashMap
import scala.text.Document

/** The class that contains elements helping in the translation to pi-like-calculus. */
trait PiCode {
  self: AnalysisUniverse =>

  import global._
  
  //TODO is there something to deal with exceptions ?

  //a call proceed on the caller side
  //(1) asking the object for the address: if overloading then use dispatchtable to ask address else use name
  //(2) receive then name for the execution
  //(3) send the arguments + this + return
  //on the calle side:
  //(1) receive the args
  //(2) create a new agents with the provided paramters
  //(3) let the agent do the rest

  class MethodExecutor(val method: Method) {

    def id = MethodExecutor.id(method)

    var includedMethod: List[Method] = Nil 

    def localVariables = method.localVariables ::: includedMethod.flatMap(_.localVariables)
    
    Logger("Plugin", LogDebug, "MethodExecutor "+this+" for " + method.symbol + " of " + method.inClass)

    def initAgent(): AgentDefinition[PC] = {
      Logger("Plugin", LogDebug, "making initial agent for " + method.symbol + " of " + method.inClass)
      //Actually the should be created with the right parameter, wha ...
      //val args = thisIdent :: returnIdent :: method.vparams.map(vd => identOfSymbol(vd.symbol))
      //val call = PatternTuple(args)
      val automatonIntermediate = method.automaton.morphFull[IA](locShortString(_), processOfTree(_))
      val thisID = Variable("this") setType typeOfSymbol(method.inClass.typeOfThis.typeSymbol)
      new AgentDefinition[String](
        MethodExecutor.id(method),
        thisChannel :: retID :: method.vparams.map(v => IDOfSymbol(v.symbol)),
        automatonIntermediate.adjacencyMap,
        automatonIntermediate.initState,
        automatonIntermediate.targetStates
      )
    }

    /** Produce the agent that corresponds to this methods execution.
     *  This is only an intermediate verion. It contains marked parts that need to be postprocessed */
    var agent: AgentDefinition[PC] = initAgent()

    var liveAt: Map[PC,Set[ID]] = Map.empty[PC,Set[ID]]
    def updateLiveAt = liveAt = liveVariables(agent)

    /** returns the objets that are created in this method. */
    def createdObjects: Set[Symbol] = {
      //inspect the edges of the agent ...
      def getCreate(p: PProcess): List[Symbol] = p match {
        case Expr(Create(clazz, _)) => PClasses.keys.find(idOfSymbol(_) == clazz).toList
        case Affect(_, cr @ Create(name, _)) => getCreate(Expr(cr))
        case PBlock(lst) => lst flatMap getCreate
        case _ => Nil
      }
      val relevantEdges = agent.cfa.edges flatMap {case (_,p,_) => getCreate(p)}
      relevantEdges.toSet
    }
  }

  object MethodExecutor {

    def id(m: Method): String = idOfSymbol(m.inClass) + "$" + idOfSymbol(m.earliestSymbol)
    def id(clazz: Symbol, s: Symbol): String = idOfSymbol(clazz) + "$" + idOfSymbol(s)

  }

  /** What you would expect if you compile an object-oriented language.
   *  The dispatch table is needed for methods called from other objects (not from the class itself).
   *  this also is the object 'in memory'
   */
  class DispatchTable(val clazz: Class) {
    //Due to inheritance, mixin and, that offests should be consistant for subtypes, the table might contains gaps.
    //def apply(s: Symbol) = DispatchTable.offsets(s)
    
    val chan = thisChannel

    var includedMethod: List[Method] = Nil 

    def localVariables: List[Symbol] = clazz.store.keys.toList ::: includedMethod.flatMap(_.localVariables)

    //simple version (names rather than offset)
    var agent: AgentDefinition[String] = {
      import scala.collection.immutable.{Map, Set}
      Logger("Plugin", LogDebug, "making initial agent for " + clazz.symbol)
      val prefix = Namer("Dispatch")// idOfSymbol(clazz.symbol) //Not sure this is guaranteed to be unique (refinedTypes) 
      val init = prefix + "$waitingForCall"
      val errors = Set.empty[String]
      val id = DispatchTable.id(clazz)
      val params = List(chan)
      //edges to add only if the class is an actor (but not for a Channel)
      val startCall = prefix + "$" + idOfSymbol(startMethod) + "$Call"
      val startDone = prefix + "$" + idOfSymbol(startMethod) + "$Done"
      val actorEdges = List(
          (init, Receive(chan, Case(idOfSymbol(  startMethod), List(returnIdent))), startCall),
          (init, Receive(chan, Case(idOfSymbol(restartMethod), List(returnIdent))), startCall),
          (startCall, Expr(Create(MethodExecutor.id(clazz.symbol, actMethod), List(chan, chan)) ), startDone),
          (startDone, Send(retID, Unit()), init)
        )
      val edges = clazz.methods.filterKeys(CallGraph.mayBeCalled).values.flatMap(m => {
        //if the class is an actor, add start + restart methods
        val name = MethodExecutor.id(m)
        val args = retID :: m.vparams.map(vd => IDOfSymbol(vd.symbol))
        val argsPat = args.map(id => if (throwAway_?(id.id)) Wildcard else PIdent(id))
        val loc = name + "$Call"
        val e1 = (init, Receive(chan, Case(idOfSymbol(DispatchTable.symbolToCall(m.symbol)), argsPat)), loc)
        val e2 = (loc, Expr(Create(name, chan :: args)), init)
        List(e1, e2)
      })
      //uses isActorClassOnly since channels don't have act methods
      val finalEdges = if (isActorClassOnly(clazz.symbol)) actorEdges ++ edges else edges
      val transitions = Labeled.listToMap[String,PProcess](finalEdges)
      new AgentDefinition[String](id, params, transitions,  init, errors)
    }
    
    var liveAt: Map[PC,Set[ID]] = Map.empty[PC,Set[ID]]
    def updateLiveAt = liveAt = liveVariables(agent)

    /** returns the objets that are created in the DispatchTable (should be none). */
    def createdObjects: Set[Symbol] = {
      //TODO assert(none) by looking at the agent
      Set.empty[Symbol]
    }

  }

  object DispatchTable {
    //is initialized in DBPTranslator
    val offsets = new HashMap[Symbol, Int]
    val toUnique = new HashMap[Symbol, Symbol]()
    var initialized = false
    //final val suffix = "$DispatchTable"
    final val suffix = "$object"
    def id(clazz: Class) = idOfSymbol(clazz.symbol) + suffix

    def symbolToCall(call: Symbol): Symbol = try {
      toUnique(call)
    } catch {
      case e:java.util.NoSuchElementException =>
        Logger("Plugin", LogError, idOfSymbol(call) + " not found in " + toStringFull)
        throw e
    }

    def toStringCommon[A](tbl: HashMap[Symbol, A], fct: Symbol => String, fct2: A => String) = {
      import scala.text._
      import scala.text.Document._
      if(!initialized) "Global dispatch table is uninitialized"
      else {
        val doc = text("Global dispatch table:") :/: group(
          ((empty: Document) /: tbl)((acc, kv) => acc :/: text(fct(kv._1) + " -> " + fct2(kv._2)))
        )
        val writer = new java.io.StringWriter
        doc.format(80, writer)
        writer.toString
      }
    }

    override def toString = toStringCommon(offsets, (s: Symbol) => s.toString, (i:Int) => i.toString)
    def toStringFull = toStringCommon(toUnique, idOfSymbol, idOfSymbol)
  }
  
  //tie everything toghether in a PClass ?
  class PClass(clazz: Class) {

    val dispatchTable = new DispatchTable(clazz)
    //var dispatchTableAgent = dispatchTable.agent
    val methods = Map[Symbol, MethodExecutor](clazz.methods.filterKeys(CallGraph.mayBeCalled).mapValues(new MethodExecutor(_)).iterator.toList:_*)
    //var methodAgents = methods.mapValues(_.agent)
    
    Logger("Plugin", LogDebug, "PClass for " + clazz.symbol + " created")

    def id = idOfSymbol(clazz.symbol)
    def symbol = clazz.symbol

    def agents = dispatchTable.agent :: methods.values.map(_.agent).toList

    //a symbol would be better ...
    def methodAgent(name: Name): AgentDefinition[PC] =
      methods.find(_._1.name == name).map(_._2.agent).get

    /** returns the symbols correspondings to the local variables of this */
    def instanceVariables = clazz.store.keys

    def processMarkupFor(a: AgentDefinition[PC]): Option[AgentDefinition[PC]] = {
      val m = removeMarking(a)
      if (m.isEmpty) Logger("Plugin", LogDebug, "processing markings " + a.id + " (unchanged)")
      else Logger("Plugin", LogDebug, "processing markings " + a.id + " (changed)")
      m
    }

    /** A return corresponds to sending a message back to the caller. */
    def putReturnsTo(m: Method, a: AgentDefinition[PC]): AgentDefinition[PC] = {
      val endState = a.id + "$end"
      val cfa2 = (a.cfa /: a.cfa.targetStates)( (cfa, s) => {
        if (m.returnSym == NoSymbol) cfa + (s, Send(retID, Unit()) , endState)
        else cfa + (s, Send(retID, IDOfSymbol(m.returnSym)), endState)
      })
      new AgentDefinition(a.id, a.params, cfa2.adjacencyMap, a.cfa.initState, Set(endState))
    }

    def postMarkup: Unit = {
      Logger("Plugin", LogDebug, "post processing (markings) " + clazz.symbol)
      for ((_,exec) <- methods) {
        val a1 = putReturnsTo(exec.method, exec.agent)
        val a2 = a1 //thisify(clazz.symbol, a1)
        val a3 = unrollBlock(a2)
        val a4 = cleanAgent(a3) 
        val a5 = a4.compact
        exec.agent = a5
      }
      //val getters = methods.keys.filter(_.isGetter)
      //val setters = methods.keys.filter(_.isSetter)
      //val ctors = methods.keys.filter(_.isPrimaryConstructor)
      //assert(ctors.size == 1, "#primaryCtor == " + ctors.size)
      //val ctor = ctors.head
      //mergeGettersSettersCtorIntoDispatch(dispatchTable,
      //                                    methods(ctor),
      //                                    getters.map(methods(_)).toList,
      //                                    setters.map(methods(_)).toList)
      dispatchTable.agent = cleanAgent(dispatchTable.agent).compact
    }

    def processMarkup: Unit = {
      var changed = false
      Logger("Plugin", LogDebug, "processing markings " + clazz.symbol)
      for ((_,exec) <- methods; a <- processMarkupFor(exec.agent)) {
        changed = true
        exec.agent = a
      }
      if (changed) processMarkup
      //else postMarkup
    }

    def updateLiveAt {
      for ((_,exec) <- methods) exec.updateLiveAt
      dispatchTable.updateLiveAt
    }

    //expand the boolean variables (cfa * store)
    //TODO to preserve uniform way of accessing the variables, the expantion should not occurs
    def expand = {
      //methodAgents = methodAgents - ctor -- getters -- setters (should not be used anymore, but has nothing to do here)
      Logger("Plugin", LogDebug, "post processing (markings) " + clazz.symbol)
      for ((_,exec) <- methods) {
        expandBooleanVariablesMethod(exec)
      }
      expandBooleanVariablesClass(dispatchTable)
    }

    def toGraphvizDoc(name: String, prefix: String): Document = {
      import scala.text.Document._
      val agentsDoc = agents.map(a => a.toGraphviz("cluster_" + a.id, "subgraph", a.id)).reduceRight(_ :/: _)
      val header = 
         if ((name startsWith "cluster_") && (prefix == "subgraph"))
           empty :: text("label = " + Misc.quote(id) + ";")
         else
           empty
      prefix :: " " :: Misc.quoteIfFancy(name) :: " {" :: nest(4, header :/: agentsDoc) :/: text("}")
    }

    /** returns the objets that are created in this class by looking
     *  at the current agents (DispatchTable + MethodExecutors) */
    def createdObjects: Set[Symbol] = {
      (dispatchTable.createdObjects /: methods.values)(_ ++ _.createdObjects)
    }

  }

  /** To store the agents. */
  object PClasses extends scala.collection.mutable.HashMap[Symbol, PClass] {

    /** removes some classes that are not used anymore (after inlining into markup) */
    def cleanup: Unit = {
      //make a creation graph and keep what is reachable from the main object
      val edges = for ((s,c) <- iterator.toList) yield c.createdObjects.map(x => (s,x))
      val graph = DiGraph[GT.ULGT{type V = Symbol}](edges.flatten).reflexiveTransitiveClosure
      val main = classes.keys.find(isMainClass(_)).get
      val allCreated = graph(main)
      val toRemove = this.keys filter (s => s.isTrait || s.isAbstractClass || (!s.isStatic && !allCreated(s)))
      Logger("Plugin", LogNotice, "PClasses cleanup removes " + toRemove.mkString("", ", ", ""))
      this --= toRemove
    }
    
    //TODO the system initial configuration:
    //creating the static objects,
    //creating a call to the main method
    //the call to main should be made only after all objects are initialized
    //BETTER: do the object alloc statically -> find in which states it might be after <init>

    def staticObjects: List[PClass] = this.filter(_._1.isModuleClass).toList.map(_._2)
    def mainClass = staticObjects.find(p => isMainClass(p.symbol))

    def toGraphviz(name: String): Document = {
      import scala.text.Document._
      val classesDoc = values.map(c => c.toGraphvizDoc("cluster_" + c.id, "subgraph")).reduceRight(_ :/: _)
      "digraph " :: Misc.quoteIfFancy(name) :: " {" :: nest(4, Document.empty :/: classesDoc) :/: text("}")
    }
    
    def toGraphvizSeparate: Iterable[(Symbol, Document)] = {
      import scala.text.Document._
      for ( (k, v) <- this) yield (k, v.toGraphvizDoc("PClass", "digraph"))
    }

  }

}
