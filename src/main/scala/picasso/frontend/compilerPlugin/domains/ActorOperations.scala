package picasso.frontend.compilerPlugin.domains

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin._
import picasso.ast.{Ident => PIdent, Process => PProcess, Block => PBlock, Value => PValue, _}
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, Wildcard => HWildcard, Binding => HBinding, _}
import picasso.graph.{GT, DiGraph, Automaton, Labeled}
import picasso.utils.Namer
import scala.tools.nsc._

trait ActorOperations {
  self: AnalysisUniverse =>

  import global._
  import global.definitions._

  /** Catches the methods that are related to actors */
  new Operations {

    def name = "ActorOperations"

    def process: PartialFunction[Tree, PProcess] = {
      //actor msg fct
      case ExActorSend(to, msg) => Send(expressionOfTree(to), addReturnAddress(expressionOfTree(msg)))
      case ExActorSendWithReturn(to, msg, replyTo) => Send(expressionOfTree(to), addReturnAddress(expressionOfTree(msg), expressionOfTree(replyTo)))
      case ExActorSendFuture(to, msg) => Logger.logAndThrow("Plugin", LogError, "PiCodeTranslator, expressionOfTree: Future not yet supported")

      case ExActorSendSync(to, msg) =>
        PBlock(List(
          Affect(sendSync, NewChannel()),
          Send(expressionOfTree(to), addReturnAddress(expressionOfTree(msg), sendSync)),
          Receive(sendSync, unpackMessageWoSender(Wildcard))
        ))
      case Assign(lhs, ExActorSendSync(to, msg)) =>
        PBlock(List(
          Affect(sendSync, NewChannel()),
          Send(expressionOfTree(to), addReturnAddress(expressionOfTree(msg), sendSync)),
          Receive(sendSync, unpackMessageWoSender(PIdent(IDOfSymbol(lhs.symbol))))
        ))
    
      case ExActorQmark(_this) => Receive(thisChannel, unpackMessageWoSender(Wildcard))
      case Assign(lhs, ExActorQmark(_this)) => Receive(thisChannel, unpackMessageWoSender(PIdent(IDOfSymbol(lhs.symbol))))
    
      //TODO nesting sender would only work if the sender is make 'owner local' (depends on the method it is in)

      //TODO receive might also directly return a value
      case ExActorReceive(_this, fct) => 
        Expr(PValue(StringVal(markup("receive", findFctInBlock(fct):_*))))
      case ExActorReceiveWithin(_this, timeout, fct) =>
        PBlock(List(
          Send(thisChannel, addReturnAddress(Application("TIMEOUT", Nil))),
          Expr(PValue(StringVal(markup("receive", findFctInBlock(fct):_*))))
        ))
    
      case ExActorReact(_this, fct) =>
        Expr(PValue(StringVal(markup("react", findFctInBlock(fct):_*))))
      case ExActorReactWithing(_this, timeout, fct) =>
        PBlock(List(
          Send(thisChannel, addReturnAddress(Application("TIMEOUT", Nil))),
          Expr(PValue(StringVal(markup("react", findFctInBlock(fct):_*))))
        ))
    
      case ExActorReply(_this, msg) =>
        Send(senderChannel, addReturnAddress(expressionOfTree(msg)))
    
      //actor ctrl flow fct
      case ExActorLoop(_this, fct) => Expr(PValue(StringVal(markup("loop", findFctInBlock(fct):_*))))
      case ExActorLoopWhile(_this, cond, fct) => Expr(PValue(StringVal(markup("loopWhile", (cond :: findFctInBlock(fct)):_*))))
      case ExActorAct(_this) => Logger.logAndThrow("Plugin", LogError, "PiCodeTranslator, expressionOfTree: act should not be directly accessed")
      //this are normal funcalls
      //case ExActorStart(_this) => Send(expressionOfTree(_this), PValue(StringVal("start")))
      //case ExActorRestart(_this) => Send(expressionOfTree(_this), PValue(StringVal("start")))
      case ExActorExit(_this, status) => Expr(PValue(StringVal(markup("exit", _this)))) //break the control flow: send message that reset the actor, then continue as 0
    }

    def expression: PartialFunction[Tree, Expression] = {
      case ExActorSender(_this) => senderChannel  // with enclosing class or method ?
    }

    /** Removing a react marking: get the function, replace the receives, substitute the args, glue it to the current cfa. */
    def removeReactMarking(a: AgentDefinition[PC], edge: (PC,(String, List[Symbol]),PC)): AgentDefinition[PC] = {
      //(actifFalse$2,(receive,List(class Actor1$lift$anonfun1, class Ping)),act$block$6)
      val (loc1, (tag, symbols), loc2) = edge
      val oldEdge = (loc1, Expr(PValue(StringVal(markupSym(tag, symbols:_*)))), loc2)
      val (classSym, args, a2) = findObjectCreation(a, symbols)
      val toAdaptReceive = createdAgentWithArgs(classSym, nme.apply, args)
      val toUnpack = instanciateArgsID(toAdaptReceive, toAdaptReceive.params.drop(2), List(thisChannel))
      val toGlue = unpackMsg(toUnpack)
      val n1 = toGlue.cfa.initState
      val n2 = toGlue.cfa.targetStates.head //size should be 1
      val cfa2 = a2.cfa.replaceEdgeBy(oldEdge, toGlue.cfa, n1, n2) //TODO not glueing
      new AgentDefinition(a2.id, a2.params, cfa2)
    }

    def removeReceiveMarking(a: AgentDefinition[PC], edge: (PC,(String, List[Symbol]),PC)): AgentDefinition[PC] = {
      //TODO receive is different since it returns a value, but for the moment ...
      removeReactMarking(a, edge)
    }
    
    /** Removing a loop marking: fetch the function, subs its args, glue it to the current automaton */
    def removeLoopMarking(a: AgentDefinition[PC], edge: (PC,(String, List[Symbol]),PC)): AgentDefinition[PC] = {
      //(act$call$2,(loop,List(class Actor1$lift$anonfun2, class Pong)),act$return$2)
      val (loc1, (tag, symbols), loc2) = edge
      val label = Expr(PValue(StringVal(markupSym(tag, symbols:_*))))
      val (classSym, args, a2) = findObjectCreation(a, symbols)
      val toGlue = createdAgentWithArgs(classSym, nme.apply, args)
      val n1 = toGlue.cfa.initState
      val n2 = toGlue.cfa.targetStates.head //size should be 1
      val looping = toGlue.cfa.morph{ case `n2` => n1 } // close the loop
      val cfa2 = a2.cfa - (loc1, label, loc2) + (loc1, Skip(), n1) ++ looping
      new AgentDefinition(a2.id, a2.params, cfa2)
    }
  
    /** Removing an exit consists of having a node to nowhere (or self loop) with Zero on the edge. */
    def removeExitMarking(a: AgentDefinition[PC], edge: (PC,(String, List[Symbol]),PC)): AgentDefinition[PC] = {
      //(act$block$15,(exit,List(class Ping)),act$block$6)
      val (loc1, (tag, symbols), loc2) = edge
      val label = Expr(PValue(StringVal(markupSym(tag, symbols:_*))))
      val endLoc = "0"
      val cfa2 = a.cfa - (loc1, label, loc2) + (loc1, Zero(), endLoc)
      //val cfa3 = cfa2.targetStates_=(cfa2.targetStates + endLoc)
      new AgentDefinition(a.id, a.params, cfa2)
    }

    def removeMarking(a: AgentDefinition[PC]): Option[AgentDefinition[PC]] = {
      val markings = marked(a)
      val (reacts, rest1) = markings.partition(_._2._1 == "react")
      val (receives, rest2) = rest1.partition(_._2._1 == "receive")
      val (loops, rest3) = rest2.partition(_._2._1 == "loop")
      val (exits, rest4) = rest3.partition(_._2._1 == "exit")
      if (reacts.isEmpty && receives.isEmpty && loops.isEmpty && exits.isEmpty) {
        None
      } else {
        val a1 = (a /: reacts)(removeReactMarking(_, _))
        val a2 = (a1 /: receives)(removeReceiveMarking(_, _))
        val a3 = (a2 /: loops)(removeLoopMarking(_, _))
        val a4 = (a3 /: exits)(removeExitMarking(_, _))
        Some(a4)
      }
      
    }

    def edgeToGraph: PartialFunction[(PClass, PC, PProcess, PC, Map[PC, Set[ID]]), Seq[PartialDBT]] = {
      case (clazz, a, p @ Zero(), "0", liveAt) => {//actor.exit
        val n1 = DBCN(a)
        val g1 = emptyConf + n1
        val g2 = emptyConf
        List((p.toString, g1, g2, Map.empty[DBC#V, DBC#V], Map.empty[DBC#V, DBC#V], None))
      }

      //TODO snafu.
      case (clazz, a, proc @ Send(dest @ ID(_), e), b, liveAt) => {
        val thisNode = unk
        val n1 = DBCN(a)
        val n2 = DBCN(b)
        val (destNode, destEdges1) = if (dest == thisChannel) accessID(n1, thisNode, dest, Some(thisNode)) else accessID(n1, thisNode, dest, None)
        //static references don't need to have an edge in the LHS graph (therefore filter with liveAt)
        val readRefs = readIDs(Expr(e)).filter(x => liveAt(a)(x)).map(id => (id,unk)).toMap
        val livesBefore = readRefs + (dest -> destNode) ++ (if (readRefs contains thisChannel) List(thisChannel -> thisNode) else Nil)
        val (m, post) = graphOfExpr(e, livesBefore)
        val g1 = makeConf(livesBefore.toList.flatMap{case (id,n) => accessID(n1,thisNode,id,n)}) + destNode //need to add dest node since static nodes don't have edges
        val livesAfter = readIDs(Send(dest, e)).filter(liveAt(b)(_)) //the ids in e are after
        //Logger("Plugin", LogDebug, "Send, liveAfter: " + livesAfter)
        val edgesAfter = 
          livesAfter.flatMap(id => accessID(n2,thisNode,id,livesBefore(id))) +
          ((m,msgDest,destNode)) ++
          (if (g1.vertices contains thisNode) accessID(n2, thisNode, thisChannel, thisNode) else Nil)
        val g2 = post ++ edgesAfter + n2
        val mapping = Map(n1 -> n2)
        val mappingBack = livesBefore.map(id => (id._2, id._2)) + (destNode -> destNode) + (thisNode -> thisNode) 
        //Logger("Plugin", LogDebug, "mappingBack: " + mappingBack)
        //Console.println("..." + (if (g1.vertices contains thisNode) accessID(n2, thisNode, thisChannel, thisNode) else Nil))
        //Console.println("g1: " + g1)
        //Console.println("g2: " + g2)
        //Console.println(" " + g1.vertices(thisNode) + ", " + g2.vertices(thisNode))
        assert(g1.vertices(thisNode) == g2.vertices(thisNode))
        List((proc.toString, g1, g2, mapping, mappingBack, None))
      }
      case (clazz, a, snd @ Send(_, _), b, liveAt) => Logger.logAndThrow("Plugin", LogError, "cannot handle anything other than ID as recipient: " + snd)
      
      //TODO snafu.
      //TODO is generating a lot of garbage (already better than dropping needed stuffs)
      case (clazz, a, proc @ Receive(src @ ID(_), pat), b, liveAt) => {
      //TODO since the destination and accessMode has changed, there is no link between the dispatcher and the thisNode ...
        val n1 = DBCN(a)
        val n2 = DBCN(b)
        val thisNode = unk
        val (srcNode, srcEdges1) = if (src == thisChannel) accessID(n1, thisNode, src, Some(thisNode)) else accessID(n1, thisNode, src, None)
        val (m, pre, map) = graphOfPattern(pat) //this should be present in LHS and RHS
        val affectedAndLives = map.filter(p => liveAt(a)(p._1))//thing that will be reaffected
        val lhsRefToNode = affectedAndLives.keys.toList.map(id => (id,unk))
        val notReferencedAfter = lhsRefToNode.map(_._2) //to add in RHS as indep nodes
        val edgesBefore = lhsRefToNode.flatMap{case (id,n) => accessID(n1,thisNode,id,n)}
        val g1 = pre ++ edgesBefore ++ srcEdges1 + (m, msgDest, srcNode) + n1
        val g2tmp = pre ++ map.toList.flatMap{case (id, that) => accessID(n2,thisNode,id,that)} ++ (if (liveAt(b)(src)) accessID(n2,thisNode,src,srcNode) else Nil)
        val g2 = ((g2tmp /: notReferencedAfter)(_ + _)) + n2 + srcNode
        val mapping = Map(n1 -> n2)
        //since the receive does not change the node, and that the pattern contians wildcard, only backward mapping
        val mappingBack = pre.vertices.map(b => (b,b)).toMap ++ notReferencedAfter.map(n => (n,n)) + (thisNode -> thisNode) + (srcNode -> srcNode)
        List((proc.toString, g1, g2, mapping, mappingBack, None))
      }
      case (clazz, a, rcv @ Receive(_, _), b, liveAt) => Logger.logAndThrow("Plugin", LogError, "cannot handle anything other than ID as receiver: " + rcv)
    }

  }

}
