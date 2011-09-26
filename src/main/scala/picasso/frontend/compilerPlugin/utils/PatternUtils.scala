package picasso.frontend.compilerPlugin.utils

import scala.tools.nsc.Global
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.utils.Namer

trait PatternUtils {
  self: TypeUtils =>

  val global: Global

  import global._
  import global.definitions._


  object RemoveBingings extends Transformer {
    override def transform(tree: Tree): Tree = tree match {
      case Bind(name, body) => super.transform(body)
      case _ => super.transform(tree)
    }
  }

  /** Removes the Bind node from a tree (pattern). */
  def removeBindings(tree: Tree): Tree = RemoveBingings.transform(tree)

  def bindingsIn(tree: Tree): List[Symbol] = {
    val finder = new FilterTreeTraverser({case Bind(_,_) => true; case _ => false})
    finder.traverse(tree)
    finder.hits.toList.map(_.symbol)
  }

  /** Takes a pattern with bindings and returns the list of assigments that corrpesongds to the bindings
   * @param enclosingSymbol the method in which the pattern is located. this is needed to create new local values
   * @param matched the values that is matched (as dent or Select), used to create the assignment
   * @param pattern the pattern that the value is supposed to match
   */
  def assignmentsOfBindings(enclosingSymbol: Symbol, matched: Tree, pattern: Tree): List[Tree] = {
    val stack = new scala.collection.mutable.Stack[(Type, Name)] //nth arg of Type
    val assignments = new scala.collection.mutable.ListBuffer[(List[(Type, Name)], Symbol)]
    def explorePattern(pattern: Tree): Unit = pattern match {
      case Bind(name, body) =>
        assignments += (stack.toList -> pattern.symbol)
        explorePattern(body)
      case Apply(id, args) =>
        val currentType = pattern.tpe
        val constructorSym = currentType.members find (_.isPrimaryConstructor) get
        val constructorType = constructorSym.tpe
        assert(constructorType.typeParams == Nil) //not a polytype (hopefully) 
        val paramsName = constructorType.params map (_.name) //better to get the name and latter find the corresponding accessor
        (paramsName zip args) foreach { case (name, argPattern) =>
          stack push (currentType -> name)
          explorePattern(argPattern)
          stack.pop
        }
      case Alternative(lst) => //no bindings inside an alternative
      case Star(stared) => //no bindings inside an alternative
      case Ident(id) => //nothing to do: normally if not already WILDCARD it was transformed into (id @ _)
      case Literal(lit) => //nothing to do
      case Typed(e,tpt) => explorePattern(e)
      case TypeTree() => //nothing to do
      case err => Logger.logAndThrow("Plugin", LogError, "PatternUtils, assignmentsOfBindings: "+err)
    }
    //from the trace, build an unfolded list of assignments
    //TODO cache prefix
    def makeAssigns(trace: (List[(Type, Name)], Symbol)): List[Tree] = {
      val fromRoot = trace._1.reverse
      val lastSym = trace._2
      val tempValues = fromRoot map (enclosingSymbol.newValue(Namer(enclosingSymbol.name + "$pattern"), pattern.pos) setInfo _._1)
      val lhsSyms = tempValues ::: List(lastSym)
      val firstRhs = if (lhsSyms.head.tpe =:= matched.tpe) matched else Apply(TypeApply(Select(matched, Any_asInstanceOf), List(TypeTree(lhsSyms.head.tpe))), List()) //casting if needed
      val tailRhs = (tempValues zip fromRoot) map {case (sym, (tpe, name)) =>
        val methodSym = getAccessorFor(tpe, name) getOrElse (Logger.logAndThrow("Plugin", LogError, tpe + " has no member called " + name))
        val returnType = methodSym.tpe.resultType
        Apply(Select(Ident(sym), methodSym), List()) setType returnType setPos pattern.pos
      } //TODO this might also need some casting
      val rhss = firstRhs :: tailRhs
      val assigns = (lhsSyms zip rhss) map {case (sym, rhs) => ValDef(sym, rhs) setPos pattern.pos}
      assigns
    }
    //
    explorePattern(pattern)
    assignments.toList flatMap makeAssigns
  }


  /** expr match pattern (needed for exception in control flow) */
  def exprMatchPattern(expr: Tree, pattern: Tree): Boolean = {
    //a simple version that just check type: that should be enough for most of the cases (at the beginning)
    expr.tpe matchesPattern pattern.tpe
    //TODO the real stuff
  }

  /** Checks if two patterns are unifiable (for disjointness). */
  def isUnifiable(p1: Tree, p2: Tree): Boolean = (p1,p2) match {
    case (Bind(_, p1), p2) => isUnifiable(p1,p2)
    case (p1, Bind(_, p2)) => isUnifiable(p1,p2)
    case (Alternative(lst), p2) => lst.exists( p1 => isUnifiable(p1,p2) )
    case (p1, Alternative(lst)) => lst.exists( p2 => isUnifiable(p1,p2) )
    case (Star(p1), Star(p2)) => true //if no element then both matches
    case (p1, p2 @ Star(_)) => isUnifiable(p2,p1) 
    case (Star(p1), p2) => isUnifiable(p1, p2) //can match if extactly one element on the left side
    case (p1 @ Ident(nme.WILDCARD), p2) => p1.tpe <:< p2.tpe || p2.tpe <:< p1.tpe
    case (p1, p2 @ Ident(nme.WILDCARD)) => p1.tpe <:< p2.tpe || p2.tpe <:< p1.tpe
    case (Ident(i1), Ident(i2)) => i1 == i2
    case (Literal(v1),Literal(v2)) => v1 == v2
    case (Apply(id1, args1), Apply(id2, args2)) =>
      args1.length == args2.length &&
      isUnifiable(id1, id2) &&
      args1.zip(args2).forall{ case (p1,p2) => isUnifiable(p1,p2) }
    case (Typed(e1,tpt1), e2) => isUnifiable(e1,e2) //TODO can really drop the 'Typed' ??
    case (e1, Typed(e2,tpt2)) => isUnifiable(e1,e2) //TODO can really drop the 'Typed' ??
    case (tt1 @ TypeTree(), tt2 @ TypeTree()) =>  tt1.tpe <:< tt2.tpe || tt2.tpe <:< tt1.tpe
    //cases that do not match
    case (Ident(_), _) | (_, Ident(_)) => false
    case (Literal(_), _) | (Literal(_), _) => false
    case (Apply(_, _), _) | (_, Apply(_, _)) => false
    case (TypeTree(), _) | (_ , TypeTree()) => false
    //TODO what about the UnApply
    case (err1,err2) => Logger.logAndThrow("Plugin", LogError, "PatternUtils, isUnifiable:("+err1+","+err2+")")
  }
  
  def allDisjointPatterns(cases: List[CaseDef]): Boolean =
    cases forall (cd1 => ! (cases exists (cd2 => cd1 != cd2 && isUnifiable(cd1.pat, cd2.pat))))

}
