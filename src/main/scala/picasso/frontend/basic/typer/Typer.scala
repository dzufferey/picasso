package picasso.frontend.basic.typer

import picasso.frontend.basic._
import picasso.graph._
import picasso.math.hol.{Bool => BoolT, Int => IntT, String => StringT, Wildcard => WildcardT, Literal => _, Application => _, _}
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}


object Typer {

  //TODO meaningfull error reporting.
  sealed abstract class TypingResult[+T]{
    def get: T
    def error: TypingResult[Nothing]
    def success: Boolean
  }
  case class TypingSuccess[T](e: T) extends TypingResult[T] {
    def get = e
    def error = sys.error("TypingSuccess.error")
    def success = true
  }
  case class TypingFailure(reason: String) extends TypingResult[Nothing] {
    //failed because of not well-formed expression
    def get = sys.error("TypingFailure.get")
    def error = this
    def success = false 
  }
  case class TypingError(reason: String) extends TypingResult[Nothing] {
    //failed because of error in the typer
    def get = sys.error("TypingError.get")
    def error = this
    def success = false 
  }
  case class TypingWentWrong(why: TypingResult[Nothing]) extends Exception

  sealed abstract class TypeConstraints {
    def apply(substitution: Map[TypeVariable, Type]): TypeConstraints
    def normalize: TypeConstraints
  }
  case object TrivialCstr extends TypeConstraints {
    def apply(substitution: Map[TypeVariable, Type]) = this
    def normalize = this
  }
  case class SingleCstr(t1: Type, t2: Type) extends TypeConstraints {
    def apply(substitution: Map[TypeVariable, Type]) = {
      SingleCstr(t1 alpha substitution, t2 alpha substitution)
    }
    def normalize = this
  }
  case class ConjCstr(lst: List[TypeConstraints]) extends TypeConstraints {
    def apply(substitution: Map[TypeVariable, Type]) = {
      ConjCstr(lst map (_(substitution)))
    }
    def normalize = {
      val nonTrivial = lst.map(_.normalize).filter(_ != TrivialCstr)
      nonTrivial match {
        case Nil => TrivialCstr
        case x :: Nil => x
        case other => ConjCstr(other)
      }
    }
  }
  case class DisjCstr(lst: List[TypeConstraints]) extends TypeConstraints {
    def apply(substitution: Map[TypeVariable, Type]) = {
      DisjCstr(lst map (_(substitution)))
    }
    def normalize = {
      val normalized = lst.map(_.normalize)
      if (normalized contains TrivialCstr) TrivialCstr
      else if (normalized.length == 1) normalized.head
      else DisjCstr(normalized)
    }
  }

  def apply(actors: Seq[Actor]): TypingResult[Seq[Actor]] = {
    //(1) scope and symbols of the Expression
    //Console.println("starting to type " + e)
    assignSymbols(actors)
    //Console.println("symbol assigned")
    //(2) extract type equations
    val (a2, eqs) = extractEquations(actors)
    if (a2.success) {
      //(3) unifies type equations
      val eqs2 = eqs.normalize
      //Console.println("equations extracted: " + eqs)
      Logger("Typer", LogDebug, "typing constraints are " + eqs2)
      val solution = solveConstraints(eqs2)
      //Console.println("able to solve equations: " + solution.isDefined)
      //(4) uses the type info to resolve the overloading and replace the types
      solution.headOption match {
        case Some(subst) =>
          Logger("Typer", LogDebug, "typing solution is " + subst)
          putTypes(a2.get, subst)
        case None => TypingFailure("cannot solve: " + eqs2)
      }
    }
    a2
  }

  def assignSymbolsToVars(a: Actor) {
    def inScope(id: ID, scope: Map[String, Symbol]) {
        assert(scope contains id.id, "not in scope: " + id)
        if (id.symbol == NoSymbol) id.symbol = scope(id.id)
        else assert(id.symbol == scope(id.id))
    }
    def binds(name: String, sym: Sym, scope: Map[String, Symbol]): Map[String, Symbol] = {
      assert(sym.symbol == NoSymbol)
      val newSym = Symbol(name)
      sym setSymbol newSym
      scope + (name -> newSym)
    }
    def processPo(proc: Process, scope: Map[String, Symbol]): Map[String, Symbol] = proc match {
      case Affect(id, value) =>
        inScope(id, scope)
        processE(value, scope)
        scope
      case Declaration(id, variable, value) =>
        processE(value, scope)
        binds(id.id, id, scope)
      case Expr(e) =>
        processE(e, scope)
      case Send(dest, content) =>
        processE(dest, scope)
        processE(content, scope)
        scope
      case Receive(cases /*List[(Expression,Pattern,Process)]*/) =>
        for  ((src, pat, proc) <- cases) {
          processE(src, scope)
          val scope2 = processPa(pat, scope)
          processPo(proc, scope2)
        }
        scope
      case Block(stmts) =>
        (scope /: stmts)((scp, p) => processPo(p, scp))
        scope
      case ITE(condition , caseTrue, caseFalse) =>
        processE(condition, scope)
        processPo(caseTrue, scope)
        processPo(caseFalse, scope)
        scope
      case While(condition , body) =>
        processE(condition, scope)
        processPo(body, scope)
        scope
      case ForEachGeneric(id, set, yieldOpt, body) =>
        processE(set, scope)
        val innerScope1 = binds(id.id, id, scope)
        val innerScope  = yieldOpt match {
          case Some((y,_)) =>
            assert(y.id != id.id)
            binds(y.id, y, innerScope1)
          case None => innerScope1
        }
        processPo(body, innerScope)
        yieldOpt match {
          case Some((_,ys)) => binds(ys.id, ys, scope)
          case None => scope
        }
    }
    def processPa(pat: Pattern, scope: Map[String, Symbol]): Map[String, Symbol] = pat match {
      case PatternLit(_) | Wildcard => scope
      case PatternTuple(lst) => (scope /: lst)((scp, e) => processPa(e, scp))
      case c @ Case(uid, args) => (scope /: args)((scp, e) => processPa(e, scp)) 
      case id @ Ident(lid) => binds(lid, id, scope)
    }
    def processE(expr: Expression, scope: Map[String, Symbol]): Map[String, Symbol] = expr match {
      case Value(_) | Any => scope
      case Create(_, args) => (scope /: args)((scp, e) => processE(e, scp))
      case Application(_, args) => (scope /: args)((scp, e) => processE(e, scp))
      case id @ ID(_) =>
        inScope(id, scope)
        scope
      case Tuple(args) => (scope /: args)((scp, e) => processE(e, scp))
    }
    val startScope = (Map.empty[String, Symbol] /: a.params)( (acc, id) => binds(id.id, id, acc) )
    processPo(a.body, startScope)
  }

  // -> there are a both interpreted fct, alg datatypes and creates ...
  // -> all those things have a global scope => should collect them first and give them unique symbols
  def assignSymbolsToApplication(actors: Seq[Actor]) {
    val actorsDef = scala.collection.mutable.HashMap[String, Symbol]()
    def actorDef(name: String, sym: Sym) {
      sym.symbol = actorsDef.getOrElseUpdate(name, Symbol(name))
    }
    val caseClasses = scala.collection.mutable.HashMap[String, Symbol]()
    def caseClass(name: String, sym: Sym) {
      sym.symbol = caseClasses.getOrElseUpdate(name, Symbol(name))
    }

    def processA(act: Actor) {
      actorDef(act.id, act)
      processPo(act.body)
    }
    def processPo(proc: Process): Unit = proc match {
      case Affect(id, value) => processE(value)
      case Declaration(id, variable, value) => processE(value)
      case Expr(e) => processE(e)
      case Send(dest, content) =>
        processE(dest)
        processE(content)
      case Receive(cases) =>
        for ((src, pat, proc) <- cases) {
          processE(src)
          processPa(pat)
          processPo(proc)
        }
      case Block(stmts) => stmts foreach processPo
      case ITE(condition, caseTrue, caseFalse) =>
        processE(condition)
        processPo(caseTrue)
        processPo(caseFalse)
      case While(condition , body) =>
        processE(condition)
        processPo(body)
      case ForEachGeneric(id, set, yieldOpt, body) =>
        processE(set)
        processPo(body)
    }
    def processPa(pat: Pattern): Unit = pat match {
      case PatternLit(_) | Wildcard | Ident(_) => ()
      case PatternTuple(lst) => lst foreach processPa
      case c @ Case(uid, args) => 
        args foreach processPa
        caseClass(uid, c)
    }
    def processE(expr: Expression): Unit = expr match {
      case Value(_) | Any | ID(_) => ()
      case Tuple(args) => args foreach processE
      case ap @ Application(fct, args) =>
        ap match {
          case Create(cls, args) => actorDef(cls, ap)
          case _ => 
            args foreach processE
            val defined = Definitions.forName(fct)
            if (defined.size > 1) Logger.logAndThrow("Typer", LogError, "no overloading for the moment ("+fct+")") 
            else if (defined.size == 1) ap.symbol = defined.head.symbol
            else caseClass(fct, ap)
        }
    }
    actors foreach processA
  }

  def assignSymbols(actors: Seq[Actor]) {
    assignSymbolsToApplication(actors)
    actors foreach assignSymbolsToVars
  }

  //TODO preserve position
  //TODO get ride of the TypingResult

  def extractEquations(actors: Seq[Actor]): (TypingResult[Seq[Actor]], TypeConstraints) = {
    val symbolToType = scala.collection.mutable.HashMap[Symbol, Type]()

    def processIdent[T <: Sym with Typed](v: T): TypeConstraints = {
      if (v.tpe == WildcardT) {
        var newTpe = symbolToType.getOrElse(v.symbol, Type.freshTypeVar)
        symbolToType += (v.symbol -> newTpe)
        v setType newTpe
        //Console.println("fresh type for " + v + " " + v.symbol + " -> " + newTpe)
        TrivialCstr
      } else {
        var oldTpe = symbolToType.getOrElse(v.symbol, v.tpe)
        symbolToType += (v.symbol -> oldTpe)
        //Console.println(v + " -> " + SingleCstr(v.tpe, oldTpe))
        SingleCstr(v.tpe, oldTpe)
      }
    }

    //TODO free type in actors ?
    def processA(a: Actor): TypeConstraints = {
      //params
      val paramsCstr = a.params map processIdent
      //represents an actor as a fct: params -> classType ? (i.e. type of Ctor)
      val actCtorType = symbolToType.getOrElseUpdate(a.symbol, Function(a.params map (_.tpe), ActorType(a.id, Nil)))
      val (argsType, actType) = actCtorType match {
        case Function(a, r) => (a, r)
        case err => Logger.logAndThrow("Typer", LogError, "Ctor type is not a fct ("+err+")") 
      }
      val applyCstr = a.params.map(_.tpe).zip(argsType).map{case (a,b) => SingleCstr(a,b)}
      //then type the body
      val bodyCstr = processPo(a.body)
      a setType actType
      ConjCstr(bodyCstr :: applyCstr ::: paramsCstr)
    }
    def processPo(proc: Process): TypeConstraints = proc match {
      case Affect(id, value) => 
        val idCstr = processIdent(id)
        val valCstr = processE(value)
        ConjCstr(List(SingleCstr(id.tpe, value.tpe), idCstr, valCstr))
      case Declaration(id, variable, value) => 
        val idCstr = processIdent(id)
        val valCstr = processE(value)
        ConjCstr(List(SingleCstr(id.tpe, value.tpe), idCstr, valCstr))
      case Expr(e) => 
        processE(e)
      case Send(dest, content) =>
        val destCstr = processE(dest)
        val contCstr = processE(content)
        ConjCstr(List(SingleCstr(dest.tpe, Channel()), destCstr, contCstr))
      case Receive(cases) =>
        val casesCstr = for ((src, pat, proc) <- cases) yield {
          val srcCstr = processE(src)
          val patCstr = processPa(pat)
          val procCstr = processPo(proc)
          ConjCstr(List(SingleCstr(src.tpe, Channel()), srcCstr, patCstr, procCstr))
        }
        ConjCstr(casesCstr)
      case Block(stmts) =>
        ConjCstr(stmts map processPo)
      case ITE(condition, caseTrue, caseFalse) =>
        val condCstr = processE(condition)
        val trueCstr = processPo(caseTrue)
        val falseCstr = processPo(caseFalse)
        ConjCstr(List(SingleCstr(condition.tpe, BoolT), condCstr, trueCstr, falseCstr))
      case While(condition , body) =>
        val condCstr = processE(condition)
        val bodyCstr = processPo(body)
        ConjCstr(List(SingleCstr(condition.tpe, BoolT), condCstr, bodyCstr))
      case ForEachGeneric(id, set, yieldOpt, body) =>
        val (param1, coll1) = Definitions.freshCollT
        val coll1Cstr = ConjCstr(List(SingleCstr(id.tpe, param1),
                                      SingleCstr(set.tpe, coll1)))
        val bodyCstr = processPo(body)
        val coll2Cstr = for ((y,ys) <- yieldOpt) yield {
          val (param2, coll2) = Definitions.freshCollT
          ConjCstr(List(SingleCstr(y.tpe, param2),
                        SingleCstr(ys.tpe, coll2)))
        }
        ConjCstr(List(coll1Cstr,bodyCstr) ++ coll2Cstr)
    }
    def processPa(pat: Pattern): TypeConstraints = pat match {
      case PatternLit(_) | Wildcard => TrivialCstr
      case t @ PatternTuple(args) => 
        val argsCstr = args map processPa
        t setType Product(args map (_.tpe))
        ConjCstr(argsCstr)
      case id @ Ident(_) => processIdent(id)
      case c @ Case(uid, args) => 
        val argsCstr = args map processPa
        val caseTpe = symbolToType.getOrElseUpdate(c.symbol, CaseType(uid, args.map(_ => Type.freshTypeVar)))
        val caseType = CaseType(uid, args.map(_.tpe))
        c setType caseType
        ConjCstr(SingleCstr(caseType, caseTpe) :: argsCstr)
    }
    def processE(expr: Expression): TypeConstraints = expr match {
      case Value(_) | Any => TrivialCstr
      case id @ ID(_) => processIdent(id)
      case t @ Tuple(args) =>
        val argsCstr = args map processE
        t setType Product(args map (_.tpe))
        ConjCstr(argsCstr)
      case ap @ Application(fct, args) =>
        ap match {
          case Create(cls, args) =>
            val argsCstr = args map processE
            val actorTpe = symbolToType.getOrElseUpdate(ap.symbol, Function(args.map(_ => Type.freshTypeVar), ActorType(cls, Nil)))
            val (argsType, returnType) = actorTpe match { //TODO what if type params
              case Function(a, r) => (a,r)
              case other => (Nil, other)
            }
            val argsTypes = args.map(_.tpe)
            val argsCstrs = argsType zip argsTypes map { case (a,b) => SingleCstr(a,b) }
            ap setType returnType
            ConjCstr(argsCstrs ::: argsCstr)
          case _ =>
            val possibilities = Definitions.forName(fct)
            val possibilities2 = possibilities.filter(_.arity == args.size)
            if (!possibilities2.isEmpty) {
              //interpreted
              val argsCstr = args map processE
              val returnT = Type.freshTypeVar
              ap setType returnT
              val argsTypes = args.map(_.tpe)
              val cases = possibilities2.map( deff => {
                val (argsType, returnType) = deff.freshCopyOfType._2 match {
                  case Function(a, r) => (a,r)
                  case other => (Nil, other)
                }
                val returnCstr = SingleCstr(returnT, returnType)
                val argsCstrs = argsType zip argsTypes map { case (a,b) => SingleCstr(a,b) }
                //Console.println(ap + " -> " + argsCstrs + " -> " + returnCstr)
                ConjCstr(returnCstr :: argsCstrs)
              })
              ConjCstr(argsCstr ::: List(DisjCstr(cases)))
            } else if (possibilities2.isEmpty && !possibilities.isEmpty) {
              //interpreted but application has wrong arity
              throw TypingWentWrong(TypingFailure(ap + " has the wrong arity"))
            } else {
              //case cls
              val argsCstr = args map processE
              val caseTpe = symbolToType.getOrElseUpdate(ap.symbol, CaseType(fct, args.map(_ => Type.freshTypeVar)))
              val caseType = CaseType(fct, args.map(_.tpe))
              ap setType caseType
               ConjCstr(SingleCstr(caseType, caseTpe) :: argsCstr)
            }
        }
    }

    try {
      val cstrs = actors map processA
      Logger("Typer", LogDebug, "symbolToType " + symbolToType.mkString("\n","\n",""))
      (TypingSuccess(actors), ConjCstr(cstrs.toList))
    } catch {
      case TypingWentWrong(err) => (err, TrivialCstr)
    }
  }


  def mergeSubst(base: Map[TypeVariable, Type], addition: Map[TypeVariable, Type]): Map[TypeVariable, Type] = {
    assert(base.keySet.intersect(addition.values.flatMap(_.freeParameters).toSet).isEmpty)
    base.map{ case (t1, t2) => (t1, t2.alpha(addition))} ++ addition
  }

  //TODO: decision stack and backtracking like a prolog interpreter 
  def solveConstraints(eqs: TypeConstraints): List[Map[TypeVariable, Type]] = eqs match {
    case TrivialCstr => List(Map.empty[TypeVariable, Type])
    case SingleCstr(t1, t2) => unify(t1, t2).toList
    case ConjCstr(lst) =>
      //TODO adapt to List
      (List(Map.empty[TypeVariable, Type]) /: lst)( (acc, cstr) => acc.flatMap( subst => {
        val cstr2 = cstr(subst)
        solveConstraints(cstr2).map( subst2 => mergeSubst(subst, subst2) )
      }))
    case DisjCstr(lst) => 
      lst.flatMap( solveConstraints(_).toList )
  }

  def unify(t1: Type, t2: Type): Option[Map[TypeVariable, Type]] = (t1,t2) match {
    case (BoolT, BoolT) | (IntT, IntT) | (StringT, StringT) | (WildcardT, _) | (_, WildcardT) =>
      Some(Map.empty[TypeVariable, Type])
    case (UnInterpreted(u1), UnInterpreted(u2)) =>
      if (u1 == u2) Some(Map.empty[TypeVariable, Type])
      else None
    case (FiniteValues(f1), FiniteValues(f2)) =>
      if (f1 == f2) Some(Map.empty[TypeVariable, Type]) //TODO better comparaison
      else None
    case (v1 @ TypeVariable(n1), v2 @ TypeVariable(n2)) =>
      Some(if (n1 == n2) Map.empty[TypeVariable, Type] else Map(v1 -> v2))
    case (v1 @ TypeVariable(_), otherType) =>
      if (otherType.freeParameters contains v1) None else Some(Map(v1 -> otherType))
    case (otherType, v1 @ TypeVariable(_)) =>
      if (otherType.freeParameters contains v1) None else Some(Map(v1 -> otherType))
    case (ClassType(cl1, tps1), ClassType(cl2, tps2)) =>
      if (cl1 == cl2) {
        assert(tps1.size == tps2.size)
        solveConstraints(ConjCstr((tps1 zip tps2).map{ case (t1,t2) => SingleCstr(t1,t2)})).headOption //TODO what if more than 1
      } else None
    case (Function(arg1, r1), Function(arg2, r2)) =>
      if (arg1.size == arg2.size)
        solveConstraints(ConjCstr(SingleCstr(r1,r2) :: (arg1 zip arg2).map{ case (t1,t2) => SingleCstr(t1,t2)})).headOption //TODO what if more than 1
      else None
    case (Product(p1), Product(p2)) =>
      if (p1.size == p2.size)
        solveConstraints(ConjCstr((p1 zip p2).map{ case (t1,t2) => SingleCstr(t1,t2)})).headOption //TODO what if more than 1
      else None
    case _ => None
  }
  
  def putTypes(actors: Seq[Actor], subst: Map[TypeVariable, Type]) {
    def processA(a: Actor) {
       a.tpe = a.tpe.alpha(subst)
       a.params foreach processE
       processPo(a.body)
    }
    def processPo(proc: Process): Unit = proc match {
      case Affect(id, value) =>
        processE(id)
        processE(value)
      case Declaration(id, variable, value) =>
        processE(id)
        processE(value)
      case Expr(e) => processE(e)
      case Send(dest, content) =>
        processE(dest)
        processE(content)
      case Receive(cases) =>
        for ((src, pat, proc) <- cases) {
          processE(src)
          processPa(pat)
          processPo(proc)
        }
      case Block(stmts) => stmts foreach processPo
      case ITE(condition, caseTrue, caseFalse) =>
        processE(condition)
        processPo(caseTrue)
        processPo(caseFalse)
      case While(condition , body) =>
        processE(condition)
        processPo(body)
      case ForEachGeneric(id, set, yieldOpt, body) =>
        processE(id)
        processE(set)
        processPo(body)
        for ((y,ys) <- yieldOpt) {
          processE(y)
          processE(ys)
        }
    }
    def processPa(pat: Pattern): Unit = pat match {
      case PatternLit(_) | Wildcard => ()
      case PatternTuple(lst) => 
        lst foreach processPa
        pat.tpe = pat.tpe.alpha(subst)
      case Case(uid, args) =>
        args foreach processPa
        pat.tpe = pat.tpe.alpha(subst)
      case Ident(_) =>
        pat.tpe = pat.tpe.alpha(subst)
    }
    def processE(expr: Expression): Unit = expr match {
      case Value(_) | Any =>
      case ID(_) =>
        expr.tpe = expr.tpe.alpha(subst)
      case Tuple(args) =>
        args foreach processE
        expr.tpe = expr.tpe.alpha(subst)
      case ap @ Application(fct, args) => //TODO overloading
        expr.tpe = expr.tpe.alpha(subst)
        val args2 = ap match {
          case Create(cls, args) => args
          case _ => args
        }
        args2 foreach processE
    }
    actors foreach processA
  }
}
