package picasso.frontend.compilerPlugin

import scala.tools.nsc._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.utils.Namer
import picasso.math.hol._
import picasso.graph.Automaton

trait PredicateAbstraction {
  self: AnalysisUniverse =>

  import global._

  /** Returns a map from symbol (scope) to predicates. */
  private def collectPredicates(clazz: Class): Map[Symbol,Iterable[Predicate]] = {
    //TODO what about predicates in methods ...
    val pred = clazz.predicates.map( p => (p.symbol.owner -> p.predicate) )
    pred.groupBy(_._1).map{ case (a,b) => (a, b map (_._2)) }
  }

  sealed abstract class PValue
  case object PBottom extends PValue
  case object PTop extends PValue
  case object PTrue extends PValue
  case object PFalse extends PValue
  type Valuation = Map[Predicate, PValue]

  private def makeTreeOfPredicate(valuation: Valuation) = {
    val assumptions = valuation.flatMap{case (p, b) => b match {
      case PTop | PBottom => None
      case PTrue => Some(p.tree)
      case PFalse => Some(ExNot(p.tree))
    }}
    val seed: Tree = Literal(true) setType definitions.BooleanClass.typeConstructor
    (seed /: assumptions)( (acc, a) => ExAnd(acc, a))
  }

  //TODO
  private def isHoarTripleValid(preCond: Tree, code: Iterable[Tree], postCond: Tree): Option[Boolean] = {
    sys.error("waiting to put back the funcheck thing ...")
  }

  private def post(before: Valuation, edge: List[Tree]): Valuation = {
    val assumption = makeTreeOfPredicate(before)
    def query(p: Predicate): PValue = {
      val q1 = isHoarTripleValid(assumption, edge, p.tree)
      if (q1.isDefined && q1.get) PTrue
      else {
        val q2 = isHoarTripleValid(assumption, edge, ExNot(p.tree))
        if (q2.isDefined && q2.get) PFalse
        //if some predicate bottom before, no symbol are en the edge (unknown after), keep it bottom 
        else if ( q1.isDefined &&
                  q2.isDefined &&
                  before(p) == PBottom &&
                  p.containing.intersect((Set[Symbol]() /: edge)((acc, e) => acc ++ symbolsIn(e) )).isEmpty)
          PBottom
        else PTop
      }
    }
    before.map{case (p, _) => (p, query(p))}
  }
  private def cover(v1: Valuation, v2: Valuation) = {
    v1.keys forall (k => (v1(k), v2(k)) match {
      case (PTop, _) => true
      case (PTrue, PTrue | PBottom) => true
      case (PFalse, PFalse | PBottom) => true
      case (PBottom, PBottom) => true
      case _ => false
    })
  }
  private def same(v1: Valuation, v2: Valuation) = cover(v1, v2) && cover(v2, v1)
  private def joinSingle(v1: PValue, v2: PValue): PValue = (v1,v2) match {
    case (PTop, _) | (_, PTop) | (PTrue, PFalse) | (PFalse, PTrue) => PTop
    case (PTrue, PTrue | PBottom) | (PBottom, PTrue) => PTrue
    case (PFalse, PFalse | PBottom) | (PBottom, PFalse) => PFalse
    case _ => PBottom
  }
  private def join(v1: Valuation, v2: Valuation): Valuation = {
    for ( (k,v) <- v1) yield (k, joinSingle(v, v2(k)))
  }

  //TODO unknown stuff that will make FunCheck complains: filter them ...
  //funcall with the code: inline
  //funcall without the code and supported: let it be
  //funcall without the code and not supported: havoc
  private def preprocessForFuncheck(clazz: Class, method: Method): Automaton[RScala] = {
    //The quick and dirty way: whenever is not supported: put a warning and replace it by unit
    //we can try toPureScala for the is supported test ... (but has the stop if error problem)
    sys.error("TODO")
  }

  /** Calling a method is some given state (predicates)
   * @returns a new state (predicates)
   */
  private def analyseMethod(clazz: Class,
                            predicates: Map[Symbol, Iterable[Predicate]],
                            init: Valuation,
                            method: Method): Valuation = {
    val scope = (method.symbol :: method.symbol.ownerChain).toSet
    val releventPreds = scope.flatMap(s => predicates.getOrElse(s, Nil))
    val initFull: Valuation = releventPreds.map(p => (p, init.getOrElse(p,PBottom))).toMap
    val emptyFull: Valuation = releventPreds.map(p => (p, PBottom)).toMap
    val compactAutomaton = method.automaton.simplePathsAutomaton
    def default(loc: RScala#V) = if (loc == compactAutomaton.initState) initFull else emptyFull
    val fixpt = compactAutomaton.aiFixpoint(post, join, cover, default)
    (emptyFull /: compactAutomaton.targetStates)( (acc, s) => join(acc, fixpt(s))) 
  }

  /** Returns the initial values of predicates after the object creation. */  
  private def initialPredicateValue(clazz: Class): Valuation = {
    val predMap = collectPredicates(clazz)
    val init = predMap.values.flatMap( lst => lst.map(_ -> PBottom)).toMap
    val ctor = clazz.primaryCtor
    analyseMethod(clazz, predMap, init, ctor)
  }

  def abstractClass(clazz: Class): Class = {
    Logger("Plugin", LogDebug, "starting predicate abstraction for " + clazz.symbol)
    val init = initialPredicateValue(clazz)
    //build a "path sensitive" automaton were edges are: preState - call -> postState
    //TODO needs to use Supported to know what can be thrown away ?
    //or keep everything and let the backend decide ?

    //for the first test, check whether there are predicates, if yes try to build an new class
    //in all case return then old class
    //sys.error("TODO")
    clazz
  }

}
