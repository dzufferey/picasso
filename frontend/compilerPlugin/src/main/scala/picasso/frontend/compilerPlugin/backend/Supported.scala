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
            assert(changePat(pat).ids.isEmpty)
            Skip()
          case src2 => Receive(src2, changePat(pat))
        }
    }
    agt.morphFull[PC]((pc: PC) => pc, changeProcess)
  }

  ///////////////////////////////////////
  //  TODO move this to somewhere else //
  ///////////////////////////////////////

  //using AI fixpoint to compute the set of value that can be at one point
  //  compute what value comes from what if a variable comes only from one source it can be propagated
  //  a value never read can be thrown away if it side effect-free (otherwise simple not affect it)
  //TODO

  //This part is also about taking into account the state of the local variables
  //this can be done independently for each method and dispatchTable (since methods modify states only through accessors)
  //basically, at each location determine the values of the boolean variables.
  //... .. .

  def liveVariables[PC](agt: AgentDefinition[PC]): Map[PC, Set[ID]] = {
    agt.liveVariables
  }

  def liveVariablesRestrictedTo[PC](syms: Iterable[Symbol], agt: AgentDefinition[PC]): Map[PC, Set[ID]] = {
    val varIDs = (syms map IDOfSymbol).toSet
    liveVariables(agt).mapValues( _ intersect varIDs)
  }

}
