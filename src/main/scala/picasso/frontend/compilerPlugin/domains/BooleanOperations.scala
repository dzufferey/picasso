package picasso.frontend.compilerPlugin.domains

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin._
import picasso.ast.{Ident => PIdent, Process => PProcess, Block => PBlock, Value => PValue, _}
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, Wildcard => HWildcard, Binding => HBinding, _}
import picasso.graph.{GT, DiGraph, Automaton, Labeled}
import picasso.utils.Namer
import scala.tools.nsc._

trait BooleanOperations {
  self: AnalysisUniverse =>

  import global._
  import global.definitions._

  /** Catches the methods that are related to boolean values */
  new Operations {

    def name = "BooleanOperations"

    def process: PartialFunction[Tree, PProcess] = new PartialFunction[Tree, PProcess]{
      def isDefinedAt(x: Tree) = false
      def apply(x: Tree) = sys.error("not defined")
    }

    def expression: PartialFunction[Tree, Expression] = {
      case ExBooleanLiteral(bool) => PValue(Bool(bool))
      case ExAnd(t1, t2) => Application("&&", List(expressionOfTree(t1), expressionOfTree(t2)) )
      case ExOr(t1,t2) => Application("||", List(expressionOfTree(t1), expressionOfTree(t2)) )
      case ExXor(t1,t2) => Application("^", List(expressionOfTree(t1), expressionOfTree(t2)) )
      case ExNot(t) => Application("!", List(expressionOfTree(t)))
    }
    
    def removeMarking(a: AgentDefinition[PC]): Option[AgentDefinition[PC]] = None
  
    //TODO
    //for boolean functions -> assumes ony one return value that is either true/false/Any
    //to deal with the Any we can have three distinct functions: isValid, isStatisfiable, evaluate (preserve Any).
    
    def makeAndLHS(methodExec: DBC#V, thisNode: DBC#V, args: List[ID]): Seq[(Boolean, DBCC, Map[ID,DBC#V])] = {
      val argsSet = args.toSet.toList //avoids multiple references to the same node
      val trueNodes = argsSet map (a => (a, matchTrueAny))
      val trueCase = makeConf(trueNodes.flatMap{ case(id, node) => accessID(methodExec, thisNode, id, node)})
      val falseNodes = argsSet map (a => (a, matchFalseAny))
      val falseCases = falseNodes map { case(id, node) => (false, makeConf(accessID(methodExec, thisNode, id, node)), Map(id -> node))}
      (true, trueCase, trueNodes.toMap) :: falseCases
    }

    def makeOrLHS(methodExec: DBC#V, thisNode: DBC#V, args: List[ID]): Seq[(Boolean, DBCC, Map[ID,DBC#V])] = {
      val argsSet = args.toSet.toList //avoids multiple references to the same node
      val falseNodes = argsSet map (a => (a, matchFalseAny))
      val falseCase = makeConf(falseNodes.flatMap{ case(id, node) => accessID(methodExec, thisNode, id, node)})
      val trueNodes = argsSet map (a => (a, matchTrueAny))
      val trueCases = trueNodes map { case(id, node) => (true, makeConf(accessID(methodExec, thisNode, id, node)), Map(id -> node))}
      (false, falseCase, falseNodes.toMap) :: trueCases
    }

    def makeNotLHS(methodExec: DBC#V, thisNode: DBC#V, arg: ID): Seq[(Boolean, DBCC, Map[ID,DBC#V])] = {
      val falseNode = Map(arg -> matchTrueAny)
      val falseCase = makeConf(falseNode.toList.flatMap{ case(id, node) => accessID(methodExec, thisNode, id, node)})
      val trueNode = Map(arg -> matchFalseAny)
      val trueCase =  makeConf(trueNode.toList.flatMap{ case(id, node) => accessID(methodExec, thisNode, id, node)})
      List((false, falseCase, falseNode), (true, trueCase, trueNode))
    }
    
    def makeIDLHS(methodExec: DBC#V, thisNode: DBC#V, arg: ID): Seq[(Boolean, DBCC, Map[ID,DBC#V])] = {
      val falseNode = Map(arg -> matchFalseAny)
      val falseCase = makeConf(falseNode.toList.flatMap{ case(id, node) => accessID(methodExec, thisNode, id, node)})
      val trueNode = Map(arg -> matchTrueAny)
      val trueCase =  makeConf(trueNode.toList.flatMap{ case(id, node) => accessID(methodExec, thisNode, id, node)})
      List((false, falseCase, falseNode), (true, trueCase, trueNode))
    }

    def makeXorLHS(methodExec: DBC#V, thisNode: DBC#V, id1: ID, id2: ID): Seq[(Boolean, DBCC, Map[ID,DBC#V])] = {
      val cases =
        if (id1 == id2) List((false, Map(id1 -> matchTrueFalseAny)))
        else
          List(
            (true, Map(id1 -> matchTrueAny, id2 -> matchFalseAny)),
            (true, Map(id1 -> matchFalseAny, id2 -> matchTrueAny)),
            (false, Map(id1 -> matchTrueAny, id2 -> matchTrueAny)),
            (false, Map(id1 -> matchFalseAny, id2 -> matchFalseAny))
          )
      cases map { case (result, map) =>
          ( result,
            makeConf(map.toList.flatMap{ case(id, node) => accessID(methodExec, thisNode, id, node)}),
            map )
      }
    }

    def makeEqLHS(methodExec: DBC#V, thisNode: DBC#V, id1: ID, id2: ID): Seq[(Boolean, DBCC, Map[ID,DBC#V])] = {
      val cases =
        if (id1 == id2) List((true, Map(id1 -> matchTrueFalseAny)))
        else
          List(
            (false, Map(id1 -> matchTrueAny, id2 -> matchFalseAny)),
            (false, Map(id1 -> matchFalseAny, id2 -> matchTrueAny)),
            (true, Map(id1 -> matchTrueAny, id2 -> matchTrueAny)),
            (true, Map(id1 -> matchFalseAny, id2 -> matchFalseAny))
          )
      cases map { case (result, map) =>
          ( result,
            makeConf(map.toList.flatMap{ case(id, node) => accessID(methodExec, thisNode, id, node)}),
            map )
      }
    }

    def makeNeLHS(methodExec: DBC#V, thisNode: DBC#V, id1: ID, id2: ID): Seq[(Boolean, DBCC, Map[ID,DBC#V])] = {
      makeXorLHS(methodExec, thisNode, id1, id2)
    }

    //TODO preserving ref correctly ??
    def makeBooleanNarrowFct(clazz: PClass, a: PC, p: Affect, b: PC, liveAt: Map[PC,Set[ID]]): Seq[(String, DBCC, DBCC, Map[DBC#V,DBC#V], Map[DBC#V,DBC#V], Option[DBCC])] = {
      val thisNode = unk
      val n1 = DBCN(a)
      val n2 = DBCN(b)
      //performs some normalisation
      val simplifyedValue = picasso.transform.BooleanFunctions.groundTermSimplification(p.value)
      val guards = simplifyedValue match {
        case Application("&&", args) => makeAndLHS(n1, thisNode, args.map{case id @ ID(_) => id; case _ => sys.error("not isBooleanFctNarrow")})
        case Application("||", args) => makeOrLHS(n1, thisNode, args.map{case id @ ID(_) => id; case _ => sys.error("not isBooleanFctNarrow")})
        case Application("^", List(e1 @ ID(_),e2 @ ID(_))) => makeXorLHS(n1, thisNode, e1, e2)
        case Application("==", List(e1 @ ID(_),e2 @ ID(_))) => makeEqLHS(n1, thisNode, e1, e2)
        case Application("!=", List(e1 @ ID(_),e2 @ ID(_))) => makeNeLHS(n1, thisNode, e1, e2)
        case Application("!", List(e @ ID(_))) => makeNotLHS(n1, thisNode, e)
        case PValue(Bool(b)) => List((b, emptyConf + n1, Map.empty[ID,DBC#V]))
        case e @ ID(_) => makeIDLHS(n1, thisNode, e)
        case err => sys.error("not isBooleanFctNarrow: " + err)
      }
      def lhsToTrs(result: Boolean, lhsPartial: DBCC, map: Map[ID,DBC#V]): PartialDBT = {
        val rhsPatial = makeConf(accessID(n2, thisNode, p.id, DBCN(result.toString)))
        makeAffect(a, b, p, liveAt,
                   thisNode, n1, n2,
                   lhsPartial, map, rhsPatial,
                   Map.empty[DBC#V, DBC#V], Map.empty[DBC#V, DBC#V])
      }
      guards.map{ case (a,b,c) => lhsToTrs(a,b,c) }
    }

    //TODO better
    def isBooleanFct(ap: Application) = ap match {
      case Application("&&", args) => args forall isSupportedForBoolean
      case Application("||", args) => args forall isSupportedForBoolean
      case Application("^", args @ List(_,_)) => args forall isSupportedForBoolean
      case Application("==", args @ List(_,_)) => args forall isSupportedForBoolean
      case Application("!=", args @ List(_,_)) => args forall isSupportedForBoolean
      case Application("!", List(e)) => isSupportedForBoolean(e)
      case _ => false
    }
    def isSupportedForBoolean(e: Expression): Boolean = e match {
      case ID(v) => canDoSomethingWith(v.tpe)
      case PValue(_) => true
      case Any => true //for unkown elements
      case ap @ Application(_, _) => isBooleanFct(ap)
      case _ => false
    }
    def isBooleanFctNarrow(ap: Application) = ap match {
      case Application("&&", args) => args forall isSupportedForBooleanNarrow
      case Application("||", args) => args forall isSupportedForBooleanNarrow
      case Application("^", args @ List(_,_)) => args forall isSupportedForBooleanNarrow
      case Application("==", args @ List(_,_)) => args forall isSupportedForBooleanNarrow
      case Application("!=", args @ List(_,_)) => args forall isSupportedForBooleanNarrow
      case Application("!", List(e)) => isSupportedForBooleanNarrow(e)
      case _ => false
    }
    def isSupportedForBooleanNarrow(e: Expression): Boolean = e match {
      case ID(v) => v.tpe == HBool
      case PValue(_) => true
      case _ => false
    }

    def edgeToGraph: PartialFunction[(PClass, PC, PProcess, PC, Map[PC, Set[ID]]), Seq[PartialDBT]] = {
      //TODO affect of variable of boolean type -> expand (true, false, any) ? to reduce tree-depth ?

      //case Affect(variable, ap @ Application(fct, args)) if isBooleanFct(ap) =>
      case (clazz, a, af @ Affect(variable, ap @ Application(fct, args)), b, liveAt) if isBooleanFctNarrow(ap) =>
        makeBooleanNarrowFct(clazz, a, af, b, liveAt)
      
      case (clazz, a, Affect(variable, Any), b, liveAt) if (variable.id.tpe == HBool) =>
        val caseTrue = transitionForEdge(clazz, a, Affect(variable, PValue(Bool(true))), b, liveAt)
        val caseFalse = transitionForEdge(clazz, a, Affect(variable, PValue(Bool(false))), b, liveAt)
        caseTrue ++ caseFalse

      //TODO assume, assert
    }
  }

}

