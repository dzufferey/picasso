package picasso.frontend.compilerPlugin.backend

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin._
import picasso.ast.{Ident => PIdent, Process => PProcess, Block => PBlock, Value => PValue, _}
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, Wildcard => HWildcard, Binding => HBinding, String => HString, _}
import picasso.graph.{GT, DiGraph, Automaton, Labeled}
import scala.tools.nsc._
import scala.collection.mutable.HashMap

//taking AgentDefinition of methods, and performing semantics simplification on them.
trait Supported {
  self: AnalysisUniverse =>

  import global._
  import global.definitions._

  //TODO case objects (skip for the moment (caught by hasCodeFor))

  //is reference ? (i.e., something that has a pointer associated to).
  //any actor, any channel, any class for which we have code BUT for case class ?
  def isReference(id: ID): Boolean = isReference(id.id)
  def isReference(f: Formula): Boolean = isReference(f.tpe)
  def isReference(t: HType): Boolean = t match {
    case ActorType(_, _) => true
    case Channel() => true
    case Collection(_, t2) => canDoSomethingWith(t2)
    case HClassType( clazz, _) =>
      //Console.println("isReference: " + clazz + " against " + classes.keys.map(idOfSymbol))
      classes.keys exists (s => idOfSymbol(s) == clazz) //hasCodeFor
    case _ => false
  }

  def isValue(id: ID): Boolean = isValue(id.id)
  def isValue(f: Formula): Boolean = isValue(f.tpe)
  def isValue(t: HType): Boolean = canDoSomethingWith(t) && !isReference(t)

  def canDoSomethingWith(id: ID): Boolean = canDoSomethingWith(id.id.tpe, id.toString)
  def canDoSomethingWith(f: Formula): Boolean = canDoSomethingWith(f.tpe, f.toString)
  def canDoSomethingWith(t: HType): Boolean = canDoSomethingWith(t, "_")
  def canDoSomethingWith(t: HType, what: String): Boolean = {
    val res = t == HBool || t == HString || isReference(t)
    //Logger("Plugin", LogDebug, "canDoSomethingWith: " + what + ": " + t + " -> " + res)
    res
  }

  def throwAway_?(id: ID): Boolean = throwAway_?(id.id)
  def throwAway_?(v: Variable): Boolean = !canDoSomethingWith(v)

  def cleanAgent[PC](agt: AgentDefinition[PC]): AgentDefinition[PC] = {
    def changeExpr(p: Expression): Expression = p match {
      case id @ ID(_) => if (throwAway_?(id)) Any else id
      case Create(what, args) => Create(what, args map changeExpr)
      case Application(fct, args) => Application(fct, args map changeExpr)
      case Tuple(values) => Tuple(values map changeExpr)
      case other => other
    }
    def changePat(p: Pattern): Pattern = p match {
      case PatternTuple(lst) => PatternTuple(lst map changePat)
      case Case(uid, args) => Case(uid, args map changePat)
      case Binding(v, p) => 
        val p2 = changePat(p)
        if (throwAway_?(v)) p2 else Binding(v, p2)
      case p => p
    }
    def changeProcess(p: PProcess): PProcess = p match {
      case PBlock(stmts) => PBlock(stmts map changeProcess)
      case Affect(id @ ID(v), value) =>
        if (throwAway_?(v)) Expr(changeExpr(value))
        else Affect(id, changeExpr(value))
      case Expr(e) => Expr(changeExpr(e))
      case Send(dest, content) =>
        changeExpr(dest) match {
          case Any =>
            Logger("Plugin", LogWarning, "cleanAgent.changeProcess: " + dest + " becomes Any. Dropping " + p)
            Skip()
          case dest2 => Send(dest2, changeExpr(content))
        }
        
      case rcv @ Receive(src, pat) =>
        changeExpr(src) match {
          case Any =>
            Logger("Plugin", LogInfo, "src become Any => throwing away: " + rcv)
            assert(idsInPattern(changePat(pat)).isEmpty)
            Skip()
          case src2 => Receive(src2, changePat(pat))
        }
    }
    agt.morphFull[PC]((pc: PC) => pc, changeProcess)
  }

  def canSkip(p: PProcess): Boolean = p match {
    case Skip() | Expr(Any) | Expr(PValue(_)) |
         Assert(PValue(Bool(true))) | Assume(PValue(Bool(true))) => true
    //TODO what about assume(Any) ?
    case _ => false
  }

  //TODO be more aggressive:
  // -variable that are not live can be thrown away
  // -variable that are always Any can be removed
  // -expended variables can be removed

  /** remove useless edge to get a smaller agent (merge nodes together) */
  def compactAgent[PC](agt: AgentDefinition[PC]): AgentDefinition[PC] = {
    //if canSkip, do not impact SCC,
    //no other outgoing edge in src or not other ingoing edge in dest
    val sccs = agt.cfa.SCC
    val mapToSCC = Map[PC,Int](( sccs.zipWithIndex.flatMap( p => p._1.map((_, p._2))) ):_*)
    val rev = agt.cfa.reverse
    def canMerge(edge: (PC, PProcess, PC)): Boolean = {
      val scc1 = mapToSCC.getOrElse(edge._1, -2) + 1 //so that there is no 0 index
      val scc2 = mapToSCC.getOrElse(edge._3, -2) + 1
      canSkip(edge._2) &&
      (scc1 == scc2 || scc1 * scc2 < 0) &&
      (agt.cfa(edge._1).size == 1 || rev(edge._3).size == 1)
    }
    //merging is removing edge + merging nodes (morph)
    val edgesToRemove = agt.cfa.edges filter canMerge
    val cfa2 = agt.cfa remEdges edgesToRemove
    val toMergeEdges = edgesToRemove.flatMap{ case (a,_,b) => List((a,b),(b,a))}
    val toMergeSCC = DiGraph[GT.ULGT{type V = PC}](toMergeEdges).SCC
    val toMergeMorphism = Map[PC,PC](toMergeSCC.flatMap(scc => scc.toList.map(_ -> scc.head)):_*)
    val cfa3 = cfa2.morph(toMergeMorphism)
    new AgentDefinition(agt.id, agt.params, cfa3)
  }

  //using AI fixpoint to compute the set of value that can be at one point
  //  compute what value comes from what if a variable comes only from one source it can be propagated
  //  a value never read can be thrown away if it side effect-free (otherwise simple not affect it)
  //TODO

  //Domains for AI
  // in term or read and write, sets of Strings can be used

  def idsInExpression(e: Expression): Set[ID] = e match {
    case PValue(_) | Any => Set.empty[ID]
    case smth @ ID(_) => Set(smth)
    case Create(_, args) => (Set.empty[ID] /: args)(_ ++ idsInExpression(_))
    case Application(fct, args) => (Set.empty[ID] /: args)(_ ++ idsInExpression(_))
    case Tuple(values) => (Set.empty[ID] /: values)(_ ++ idsInExpression(_))
  }
  def idsInPattern(p: Pattern): Set[ID] = p match {
    case PatternLit(_) | Wildcard => Set.empty[ID]
    case PatternTuple(lst) => (Set.empty[ID] /: lst)(_ ++ idsInPattern(_))
    case Case(uid, args) => (Set.empty[ID] /: args)(_ ++ idsInPattern(_))
    case Binding(lid, p2) => idsInPattern(p2) + lid
  }
  def readIDs(p: PProcess): Set[ID] = p match {
    case PBlock(stmts) => (Set.empty[ID] /: stmts)(_ ++ readIDs(_))
    case Affect(_, value) => idsInExpression(value)
    case Expr(e) => idsInExpression(e)
    case Send(dest, content) => idsInExpression(dest) ++ idsInExpression(content)
    case Receive(src, _) => idsInExpression(src)
  }
  def writtenIDs(p: PProcess): Set[ID] = p match {
    case PBlock(stmts) => (Set.empty[ID] /: stmts)(_ ++ writtenIDs(_))
    case Affect(id, _) => Set(id)
    case Expr(_) | Send(_, _) => Set.empty[ID]
    case Receive(_, pat) => idsInPattern(pat)
  }


  //only correct if there are no blocks
  def postWritten(written: Set[ID], p: PProcess): Set[ID] = {
    val w = writtenIDs(p)
    written ++ w //reading does not change since it can happen multiple times
  }
  //only correct if there are no blocks
  //write "cancels" read
  def preRead(read: Set[ID], p: PProcess): Set[ID] = {
    val r = readIDs(p)
    val w = writtenIDs(p)
    read -- w ++ r
  }

  //This part is also about taking into account the state of the local variables
  //this can be done independently for each method and dispatchTable (since methods modify states only through accessors)
  //basically, at each location determine the values of the boolean variables.
  //... .. .

  //defaultValue: at the initState, the argument are written!
  def writeMap[PC](agt: AgentDefinition[PC]): Map[PC, Set[ID]] = {
    def default(s: PC) = if (s == agt.cfa.initState) agt.params.toSet
                         else Set.empty[ID]
    agt.cfa.aiFixpoint( postWritten,
                        ((a: Set[ID], b: Set[ID]) => a ++ b),
                        ((a: Set[ID], b: Set[ID]) => b subsetOf a),
                         default)
  }

  def readMap[PC](agt: AgentDefinition[PC]): Map[PC, Set[ID]] = 
    agt.cfa.aiFixpointBackward( preRead,
                                ((a: Set[ID], b: Set[ID]) => a ++ b),
                                ((a: Set[ID], b: Set[ID]) => b subsetOf a),
                                (_ => Set.empty[ID]) )

  def liveVariables[PC](agt: AgentDefinition[PC]): Map[PC, Set[ID]] = {
    //it is very likely that the read map is sufficient ...
    val read = readMap(agt)
    val written = writeMap(agt)
    assert(written.keySet == read.keySet)
    read.map{ case (k,v) => (k, v intersect written(k))}
  }

  def liveVariablesRestrictedTo[PC](syms: Iterable[Symbol], agt: AgentDefinition[PC]): Map[PC, Set[ID]] = {
    val varIDs = (syms map IDOfSymbol).toSet
    liveVariables(agt).mapValues( _ intersect varIDs)
  }

  def liveBooleanVariables[PC](m: Method, agt: AgentDefinition[PC]): Map[PC, Set[ID]] = {
    val booleanVars = m.localVariables.filter(isBoolean(_))
    liveVariablesRestrictedTo(booleanVars, agt)
  }

}
