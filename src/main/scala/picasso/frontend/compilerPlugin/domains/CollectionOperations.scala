package picasso.frontend.compilerPlugin.domains

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin._
import picasso.ast.{Ident => PIdent, Process => PProcess, Block => PBlock, Value => PValue, _}
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, Wildcard => HWildcard, Binding => HBinding, _}
import picasso.graph.{GT, DiGraph, Automaton, Labeled}
import picasso.utils.Namer
import scala.tools.nsc._

trait CollectionOperations {
  self: AnalysisUniverse =>

  import global._
  import global.definitions._

  /** Catches the methods that are related to collections */
  new Operations {

    def name = "CollectionOperations"

    //TODO this should also catch the affect for immutable collections (which are in fact like a copy)

    def process: PartialFunction[Tree, PProcess] = {
      case Assign(lhs, ExCollectionNew(clazz, Nil)) => Affect(IDOfSymbol(lhs.symbol), EmptySet())
      case Assign(lhs, ExCollectionNew(clazz, args)) =>
        val tpe = typeOfSymbol(lhs.symbol)
        val readFrom = args map (_ => ID(Variable(Namer("new"+clazz)) setType tpe))
        val storeIn = readFrom.drop(1) :+ IDOfSymbol(lhs.symbol)
        val stmts = (args zip readFrom zip storeIn) map {case ((a,r), s) => Affect(s, SetAdd(r,expressionOfTree(a)))}
        PBlock(Affect(readFrom.head, EmptySet()) :: stmts)
      case Assign(lhs, ExCollectionMap(obj, fct)) => Expr(PValue(StringVal(markup("map", (lhs :: obj :: findFctInBlock(fct)):_*))))
      case ExCollectionForeach(obj, fct) => Expr(PValue(StringVal(markup("foreach", (obj :: findFctInBlock(fct)):_*))))
      case Assign(lhs, ExCollectionFold(obj, acc, fct)) => sys.error("TODO")
      case Assign(lhs, ExCollectionReduce(obj, acc, fct)) => sys.error("TODO")
      case Assign(lhs, ExCollectionPlusPlus(obj1, obj2)) => sys.error("TODO")
      case Assign(lhs, ExCollectionMinusMinus(obj1, obj2)) => sys.error("TODO")
      case Assign(lhs, ExCollectionFilter(obj, fct)) => sys.error("TODO")
      case Assign(lhs, ExCollectionFilterNot(obj, fct)) => sys.error("TODO")
      case ExCollectionPlusPlusEqual(obj1, obj2) => sys.error("TODO")
    }
    
    def expression: PartialFunction[Tree, Expression] = {
      case ExCollectionNew(clazz, Nil) => EmptySet()
      case t @ ExCollectionNew(clazz, args) => 
        Logger.logAndThrow("Plugin", LogWarning, "new collection with arguments should be caught by process ("+t+").")
      case ExCollectionIsEmpty(obj) => SetIsEmpty(expressionOfTree(obj))
      case ExCollectionPlus(obj1, obj2) => SetAdd(expressionOfTree(obj1), expressionOfTree(obj2))
      case ExCollectionPlusColon(obj1, obj2) => SetAdd(expressionOfTree(obj1), expressionOfTree(obj2))
      case ExCollectionColonPlus(obj1, obj2) => SetAdd(expressionOfTree(obj1), expressionOfTree(obj2))
      case ExCollectionCons(obj1, obj2) => SetAdd(expressionOfTree(obj1), expressionOfTree(obj2))
      case ExCollectionPlusEqual(obj1, obj2) => SetAdd(expressionOfTree(obj1), expressionOfTree(obj2))
      case ExCollectionMinus(obj1, obj2) => SetMinus(expressionOfTree(obj1), expressionOfTree(obj2))
      case ExCollectionApply(obj, idx) =>
        Logger("Plugin", LogWarning, "collection.apply is assumed to be in range, and also not taking order into account.")
        SetChoose(expressionOfTree(obj))
      case ExCollectionHead(obj) => SetChoose(expressionOfTree(obj))
    }

    def makeBlock(lst: List[PProcess]): PProcess = lst match {
      case Nil => Skip()
      case x :: Nil => x
      case xs => PBlock(xs)
    }

    /** make loop generic that can be used for map/foreach/fold/...
     * Since it is consuming the collection, it assumes that is it alone working on it ...
     */
    def makeLoop( a: AgentDefinition[PC],
                  label: PProcess, //for the edge that needs to be removed.
                  loc1: PC,
                  loc2: PC,
                  pre: List[PProcess],
                  collection: ID, //the collection that is iterated over
                  copyBack: Boolean, //copy the collection back into ID at the end (in case it is still live)
                  process: ID => List[PProcess],
                  post: List[PProcess]
                ): AgentDefinition[PC] = {
      val collectionType = collection.id.tpe
      val typeOfElements = collectionType match {
        case Collection(_, param) => param
        case other => Logger.logAndThrow("Plugin", LogError, "unexpected collectionType: " + other)
      }
      val inter = Namer("iteration")
      val picked = ID(Variable(Namer("iterProcessingPre")) setType typeOfElements)
      val tmp = ID(Variable(Namer("iterCopyBack")) setType collectionType)

      val preCopy = pre ::: (if (copyBack) List(Affect(tmp, EmptySet())) else Nil)
      val preEdge = (loc1, makeBlock(preCopy), inter) 
      
      val loopBody = Affect(picked, SetPick(collection)) :: (if (copyBack) List(Expr(SetAdd(tmp,picked))) else Nil) ::: process(picked)
      val loopEdge = (inter, makeBlock(loopBody), inter)
      
      val postCopy = Assume(SetIsEmpty(collection)) :: (if (copyBack) List(Affect(collection, tmp)) else Nil) ::: post
      val postEdge = (inter, makeBlock(postCopy), loc2)
      
      val cfa2 = a.cfa - (loc1, label, loc2) + preEdge + loopEdge + postEdge
      new AgentDefinition(a.id, a.params, cfa2)
    }

    //TODO this translation consumes the collection ...
    //TODO assumes that SetAdd has side-effect.
    def removeMapMarking(a: AgentDefinition[PC], edge: (PC,(String, List[Symbol]),PC)): AgentDefinition[PC] = {
      val (loc1, (tag, symbols), loc2) = edge
      val label = Expr(PValue(StringVal(markupSym(tag, symbols:_*))))//TODO there might be a more elegant way to recover this ...
      assert(symbols.length == 3)
      val lhs = symbols(0)
      val obj = symbols(1)
      val objID = IDOfSymbol(obj)
      val mapper = symbols(2)
      val (callee, toCall) = findCalleeAndMethod(a, mapper)
      val collectionType = typeOfSymbol(obj) 
      val typeOfElementsAfter = typeOfType(returning(toCall))
      val collectionTypeAfter = collectionType match {
        case c @ HClassType(col, _) => 
          val ct = HClassType(col, List(typeOfElementsAfter))
          ct.isActor = c.isActor
          ct.isCollection = true
          ct.isCase = c.isCase
          ct.isModule = false
          ct
        case other => Logger.logAndThrow("Plugin", LogError, "unexpected collectionType: " + other)
      }
      Logger("Plugin", LogDebug, "removeMapMarking: from " + collectionType + " -"+callee+"."+toCall+"-> " + collectionTypeAfter + " ("+typeOfElementsAfter+")")
      val tmp = ID(Variable(Namer("mapResult")) setType collectionTypeAfter)
      val processedVar = Variable(Namer("mapProcessingPost")) setType typeOfElementsAfter
      val processed = ID(processedVar)
      val processedPat = PIdent(processed)
      //decalre result as emptyset,
      val pre = List(Affect(tmp, EmptySet()))
      val post = List(Affect(IDOfSymbol(lhs), tmp))
      def process(picked: ID) = makeFctCall(Nil, callee, toCall, List(picked), processedPat, List(Expr(SetAdd(tmp, processed)))).stmts
      val liveAfter = false //TODO true is a safe choice, but in term of speed ... So for the moment say false
      makeLoop( a, label, loc1, loc2, pre, objID, liveAfter, process, post)
    }

    def removeForeachMarking(a: AgentDefinition[PC], edge: (PC,(String, List[Symbol]),PC)): AgentDefinition[PC] = {
      val (loc1, (tag, symbols), loc2) = edge
      val label = Expr(PValue(StringVal(markupSym(tag, symbols:_*))))//TODO there might be a more elegant way to recover this ...
      assert(symbols.length == 2)
      val obj = symbols(0)
      val objID = IDOfSymbol(obj)
      val fct = symbols(1)
      val (callee, toCall) = findCalleeAndMethod(a, fct)
      def process(picked: ID) = makeFctCall(Nil, callee, toCall, List(picked), Wildcard, Nil).stmts
      val liveAfter = false //TODO true is a safe choice, but in term of speed ... So for the moment say false
      makeLoop( a, label, loc1, loc2, Nil, objID, liveAfter, process, Nil)
    }
    
    def removeMarking(a: AgentDefinition[PC]): Option[AgentDefinition[PC]] = {
      val markings = marked(a)
      val (maps, rest1) = markings.partition(_._2._1 == "map")
      val (foreachs, rest2) = rest1.partition(_._2._1 == "foreach")
      if (maps.isEmpty && foreachs.isEmpty) {
        None
      } else {
        val a1 = (a /: maps)(removeMapMarking(_, _))
        val a2 = (a1 /: foreachs)(removeForeachMarking(_, _))
        Some(a2)
      }
    }

    /* 'indirect' encoding of collections: have a special collection node
     * rather than having multiple outgoing edges from the node that have the collection.
     */
    def edgeToGraph: PartialFunction[(PClass, PC, PProcess, PC, Map[PC, Set[ID]]), Seq[PartialDBT]] = {
      case (clazz, a, af @ Affect(variable, EmptySet()), b, liveAt) => {
        val thisNode = unk
        val collectionNode = defaultCollectionNode
        val n1 = DBCN(a)
        val n2 = DBCN(b)
        val g1 = emptyConf + n1
        val g2 = makeConf(accessID(n2,thisNode,variable,collectionNode))
        val tr = makeAffect(a, b, af, liveAt,
                            thisNode, n1, n2,
                            g1, Map.empty[ID, DBC#V], g2,
                            Map.empty[DBC#V, DBC#V], Map.empty[DBC#V, DBC#V])
        List(tr)
      }

      //this assumes that set is live after
      case (clazz, a, proc @ Expr(SetAdd(set @ ID(_),obj @ ID(_))), b, liveAt) => {
        val thisNode = unk
        val collectionNode = unk
        val n1 = DBCN(a)
        val n2 = DBCN(b)
        val (objNode, objEdge1) = accessID(n1,thisNode,obj,None)
        val mapping = Map(n1 -> n2)
        val mappingBack = Map(thisNode -> thisNode, collectionNode -> collectionNode, objNode -> objNode)
        val g1 = makeConf(accessID(n1,thisNode,set,collectionNode) ++ objEdge1)
        val g2 = makeConf(accessID(n2,thisNode,set,collectionNode)) + (collectionNode, collectionMember(set.id), objNode)
        val g2p = g2 ++ (if (liveAt(b)(obj)) accessID(n2,thisNode,obj,objNode) else Nil) ++ (if (g1.vertices(thisNode)) List((n2,thisVar,thisNode)) else Nil)
        List((proc.toString, g1, g2p, mapping, mappingBack, None))
      }
      
      //even tough setAdd is a mutable operation, the result might be affected to somwhere ...
      case (clazz, a, af @ Affect(variable, SetAdd(set @ ID(_),obj @ ID(_))), b, liveAt) => {
        val thisNode = unk
        val collectionNode = unk
        val n1 = DBCN(a)
        val n2 = DBCN(b)
        val (objNode, objEdge1) = accessID(n1,thisNode,obj,None)
        val mappingBack = Map(thisNode -> thisNode, collectionNode -> collectionNode, objNode -> objNode)
        val g1 = makeConf(accessID(n1,thisNode,set,collectionNode) ++ objEdge1)
        val g2 = makeConf(accessID(n2,thisNode,set,collectionNode)) + (collectionNode, collectionMember(set.id), objNode)
        val tr = makeAffect(a, b, af, liveAt,
                            thisNode, n1, n2,
                            g1, Map(obj -> objNode, set -> collectionNode), g2,
                            Map.empty[DBC#V, DBC#V], mappingBack)
        List(tr)
      }

      //this assumes that set is live after
      //TODO as affect ?
      case (clazz, a, proc @ Expr(SetMinus(set @ ID(_), obj @ ID(_))), b, liveAt) => {
        val thisNode = unk
        val collectionNode = unk
        val n1 = DBCN(a)
        val n2 = DBCN(b)
        val (objNode, objEdge1) = accessID(n1,thisNode,obj,None)
        val mapping = Map(n1 -> n2)
        val mappingBack = Map(thisNode -> thisNode, collectionNode -> collectionNode, objNode -> objNode)
        val g1 = makeConf(accessID(n1,thisNode,set,collectionNode)) ++ objEdge1 +
                          (collectionNode,collectionMember(set.id),objNode)
        val g2 = makeConf(accessID(n2,thisNode,set,collectionNode)) ++
                 (if (liveAt(b)(obj)) accessID(n2,thisNode,obj,objNode) else Nil) ++
                 (if (g1.vertices(thisNode)) List((n2,thisVar,thisNode)) else Nil) +
                 objNode //in case it is not live after
        List((proc.toString, g1, g2, mapping, mappingBack, None))
      }
      case (clazz, a, other @ Expr(SetAdd(_,_)), b, liveAt) => Logger.logAndThrow("Plugin", LogError, "needs ID as arguments of " + other)

      //this assumes that set is live after
      case (clazz, a, proc @ Affect(variable, SetChoose(set @ ID(_))), b, liveAt) => {
        val thisNode = unk
        val collectionNode = unk
        val objNode = unk
        val n1 = DBCN(a)
        val n2 = DBCN(b)
        val mappingBack = Map(collectionNode -> collectionNode, objNode -> objNode)
        val g1 = makeConf(accessID(n2,thisNode,set,collectionNode)) + (collectionNode,collectionMember(set.id),objNode)
        val g2 = makeConf(accessID(n2,thisNode,set,collectionNode)) ++ accessID(n2,thisNode,variable,objNode) + (collectionNode,collectionMember(set.id),objNode)
        val tr = makeAffect(a, b, proc, liveAt,
                            thisNode, n1, n2,
                            g1, Map(set -> collectionNode), g2,
                            Map.empty[DBC#V, DBC#V], mappingBack)
        List(tr)
      }
      case (clazz, a, other @ Affect(variable, SetChoose(_)), b, liveAt) => Logger.logAndThrow("Plugin", LogError, "needs ID as arguments of " + other)

      case (clazz, a, proc @ Affect(variable, SetPick(set @ ID(_))), b, liveAt) => {
        //like choose but remove the element from the collection.
        val thisNode = unk
        val collectionNode = unk
        val objNode = unk
        val n1 = DBCN(a)
        val n2 = DBCN(b)
        val mappingBack = Map(collectionNode -> collectionNode, objNode -> objNode)
        val g1 = makeConf(accessID(n1,thisNode,set,collectionNode)) + (collectionNode,collectionMember(set.id),objNode)
        val g2 = makeConf(accessID(n2,thisNode,set,collectionNode)) ++ accessID(n2,thisNode,variable,objNode)
        val tr = makeAffect(a, b, proc, liveAt,
                            thisNode, n1, n2,
                            g1, Map(set -> collectionNode), g2,
                            Map.empty[DBC#V, DBC#V], mappingBack)
        List(tr)
      }
      case (clazz, a, other @ Affect(variable, SetPick(_)), b, liveAt) => Logger.logAndThrow("Plugin", LogError, "needs ID as arguments of " + other)
    }

  }
}
