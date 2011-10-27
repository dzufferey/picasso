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
      val solution = solveConstraints(eqs2)
      //Console.println("able to solve equations: " + solution.isDefined)
      //(4) uses the type info to resolve the overloading and replace the types
      solution.headOption match {
        case Some(subst) => putTypes(a2.get, subst)
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

  def extractEquations(actors: Seq[Actor]): (TypingResult[Seq[Actor]], TypeConstraints) = {
    val symbolToType = scala.collection.mutable.HashMap[Symbol, Type]()

    def processIdent[T <: Sym with Typed](v: T): (TypingResult[T], TypeConstraints) = {
      if (v.tpe == Wildcard) {
        var newTpe = symbolToType.getOrElse(v.symbol, Type.freshTypeVar)
        symbolToType += (v.symbol -> newTpe)
        //Console.println("fresh type for " + v + " " + v.symbol + " -> " + newTpe)
        (TypingSuccess(v setType newTpe), TrivialCstr)
      } else {
        var oldTpe = symbolToType.getOrElse(v.symbol, v.tpe)
        symbolToType += (v.symbol -> oldTpe)
        //Console.println(v + " -> " + SingleCstr(v.tpe, oldTpe))
        (TypingSuccess(v), SingleCstr(v.tpe, oldTpe))
      }
    }

    //TODO free type in actors ?
    def processA(a: Actor): (TypingResult[Actor], TypeConstraints) = {
      //params
      val (paramsTResult, paramsCstr) = (a.params map processIdent).unzip
      val typedID = paramsTResult.map(_.get)
      //represents an actor as a fct: params -> classType ? (i.e. type of Ctor)
      val actCtorType = symbolToType.getOrElseUpdate(a.symbol, Function(typedID map (_.tpe), ActorType(a.id, Nil)))
      val actType = actCtorType match {
        case Function(_, r) => r
        case err => Logger.logAndThrow("Typer", LogError, "Ctor type is not a fct ("+err+")") 
      }
      //then type the body
      val (bodyTR, bodyCstr) = processPo(a.body)
      if (bodyTR.success) {
        val a2 = Actor(a.id, typedID, bodyTR.get) setType actType setSymbol a.symbol
        (TypingSuccess(a2), ConjCstr(bodyCstr :: paramsCstr))
      } else {
        (bodyTR.error, TrivialCstr)
      }
    }
    def processPo(proc: Process): (TypingResult[Process], TypeConstraints) = proc match {
      case Affect(id, value) => 
        val (idTR, idCstr) = processIdent(id)
        val (valTR, valCstr) = processE(value)
        if (idTR.success) {
          if (valTR.success) {
            val id2 = idTR.get
            val val2 = valTR.get
            (TypingSuccess(Affect(id2, val2)), ConjCstr(List(SingleCstr(id2.tpe, val2.tpe), idCstr, valCstr)))
          } else (valTR.error, TrivialCstr)
        } else (idTR.error, TrivialCstr)
      case Declaration(id, variable, value) => 
        val (affTR, affCstr) = processPo(Affect(id, value))
        affTR match {
          case TypingSuccess(Affect(i, v)) => (TypingSuccess(Declaration(i,variable,v)), affCstr)
          case _ => (affTR.error, TrivialCstr)
        }
      case Expr(e) => 
        val (eTR, eCstr) = processE(e)
        if (eTR.success) (TypingSuccess(Expr(eTR.get)), eCstr)
        else (eTR.error, TrivialCstr)
      case Send(dest, content) =>
        val (destTR, destCstr) = processE(dest)
        val (contTR, contCstr) = processE(content)
        if (destTR.success) {
          if (contTR.success) {
            (TypingSuccess(Send(destTR.get, contTR.get)), ConjCstr(List(SingleCstr(destTR.get.tpe, Channel()), destCstr, contCstr)))
          } else (destTR.error, TrivialCstr)
        } else (contTR.error, TrivialCstr)
      case Receive(cases) =>
        val casesTR = for ((src, pat, proc) <- cases) yield {
          val (srcTR, srcCstr) = processE(src)
          val (patTR, patCstr) = processPa(pat)
          val (procTR, procCstr) = processPo(proc)
          if (srcTR.success) {
            if (patTR.success) {
              if (procTR.success) {
                (TypingSuccess((srcTR.get, patTR.get, procTR.get)), ConjCstr(List(SingleCstr(srcTR.get.tpe, Channel()), srcCstr, patCstr, procCstr)))
              } else (procTR.error, TrivialCstr)
            } else (patTR.error, TrivialCstr)
          } else (srcTR.error, TrivialCstr)
        }
        val (casesTyped, casesCstr) = casesTR.unzip
        if (casesTyped forall (_.success)) {
          (TypingSuccess(Receive(casesTyped.map(_.get))), ConjCstr(casesCstr))
        } else {
          (casesTyped.find(r => !r.success).get.error, TrivialCstr)
        }
      case Block(stmts) =>
        val (stmtsTR, stmtsCstr) = (stmts map processPo).unzip
        if (stmtsTR forall (_.success)) (TypingSuccess(Block(stmtsTR map (_.get))), ConjCstr(stmtsCstr))
        else (stmtsTR.find(r => !r.success).get, TrivialCstr)
      case ITE(condition, caseTrue, caseFalse) =>
        val (condTR, condCstr) = processE(condition)
        val (trueTR, trueCstr) = processPo(caseTrue)
        val (falseTR, falseCstr) = processPo(caseFalse)
        if (condTR.success) {
          if (trueTR.success) {
            if (falseTR.success) {
              (TypingSuccess(ITE(condTR.get, trueTR.get, falseTR.get)), ConjCstr(List(SingleCstr(condTR.get.tpe, BoolT), condCstr, trueCstr, falseCstr)))
            } else (falseTR, TrivialCstr)
          } else (trueTR, TrivialCstr)
        } else (condTR.error, TrivialCstr)
      case While(condition , body) =>
        val (condTR, condCstr) = processE(condition)
        val (bodyTR, bodyCstr) = processPo(body)
        if (condTR.success) {
          if (bodyTR.success) {
            (TypingSuccess(While(condTR.get, bodyTR.get)), ConjCstr(List(SingleCstr(condTR.get.tpe, BoolT), condCstr, bodyCstr)))
          } else (bodyTR, TrivialCstr)
        } else (condTR.error, TrivialCstr)
      case ForEachGeneric(id, set, yieldOpt, body) =>
        sys.error("TODO") //TODO
    }
    def processPa(pat: Pattern): (TypingResult[Pattern], TypeConstraints) = pat match {
      case v @ PatternLit(_) => (TypingSuccess(v), TrivialCstr)
      case Wildcard => (TypingSuccess(Wildcard), TrivialCstr)
      case PatternTuple(args) => 
        val (argsTR, argsCstr) = (args map processPa).unzip
        if (argsTR forall (_.success)) {
          val argsTyped = argsTR map (_.get)
          val tupleT = Product(argsTyped map (_.tpe))
          (TypingSuccess(PatternTuple(argsTyped) setType tupleT), ConjCstr(argsCstr))
        } else {
          (argsTR.find(r => !r.success).get, TrivialCstr)
        }
      case id @ Ident(_) => processIdent(id)
      case c @ Case(uid, args) => 
        val (argsTR, argsCstr) = (args map processPa).unzip
        val caseTpe = symbolToType.getOrElseUpdate(c.symbol, CaseType(uid, args.map(_ => Type.freshTypeVar)))
        if (argsTR forall (_.success)) {
          val argsTyped = argsTR map (_.get)
          val caseType = CaseType(uid, argsTyped.map(_.tpe))
          val typed = Case(uid, argsTyped) setType caseType setSymbol c.symbol
          (TypingSuccess(typed), ConjCstr(SingleCstr(caseType, caseTpe) :: argsCstr))
        } else {
          (argsTR.find(r => !r.success).get, TrivialCstr)
        }
    }
    def processE(expr: Expression): (TypingResult[Expression], TypeConstraints) = expr match {
      case v @ Value(_) => (TypingSuccess(v), TrivialCstr)
      case Any => (TypingSuccess(Any), TrivialCstr)
      case id @ ID(_) => processIdent(id)
      case Tuple(args) =>
        val (argsTR, argsCstr) = (args map processE).unzip
        if (argsTR forall (_.success)) {
          val argsTyped = argsTR map (_.get)
          val tupleT = Product(argsTyped map (_.tpe))
          (TypingSuccess(Tuple(argsTyped) setType tupleT), ConjCstr(argsCstr))
        } else {
          (argsTR.find(r => !r.success).get, TrivialCstr)
        }
      case ap @ Application(fct, args) =>
        ap match {
          case Create(cls, args) =>
            val (argsTR, argsCstr) = (args map processE).unzip
            val actorTpe = symbolToType.getOrElseUpdate(ap.symbol, Function(args.map(_ => Type.freshTypeVar), ActorType(cls, Nil)))
            val (argsType, returnType) = actorTpe match { //TODO what if type params
              case Function(a, r) => (a,r)
              case other => (Nil, other)
            }
            if (argsTR forall (_.success)) {
              val unwrappedArgs = argsTR.map(_.get)
              val argsTypes = unwrappedArgs.map(_.tpe)
              val argsCstrs = argsType zip argsTypes map { case (a,b) => SingleCstr(a,b) }
              val ap2 = Create(cls, unwrappedArgs) setSymbol ap.symbol setType returnType
              (TypingSuccess(ap2), ConjCstr(argsCstrs))
            } else {
              (argsTR.find(r => !r.success).get, TrivialCstr)
            }
          case _ =>
            val possibilities = Definitions.forName(fct)
            val possibilities2 = possibilities.filter(_.arity == args.size)
            if (!possibilities2.isEmpty) {
              //interpreted
              val (argsTR, argsCstr) = (args map processE).unzip
              if (argsTR forall (_.success)) {
                val returnT = Type.freshTypeVar
                val unwrappedArgs = argsTR.map(_.get)
                val a2 = Application(fct, unwrappedArgs) setType returnT setSymbol ap.symbol
                val argsTypes = unwrappedArgs.map(_.tpe)
                val cases = possibilities2.map( deff => {
                  val (argsType, returnType) = deff.freshCopyOfType._2 match {
                    case Function(a, r) => (a,r)
                    case other => (Nil, other)
                  }
                  val returnCstr = SingleCstr(returnT, returnType)
                  val argsCstrs = argsType zip argsTypes map { case (a,b) => SingleCstr(a,b) }
                  //Console.println(a + " -> " + argsCstrs + " -> " + returnCstr)
                  ConjCstr(returnCstr :: argsCstrs)
                })
                val cstr = ConjCstr(argsCstr ::: List(DisjCstr(cases)))
                (TypingSuccess(a2), cstr)
              } else {
                (argsTR.find(r => !r.success).get, TrivialCstr)
              }
            } else if (possibilities2.isEmpty && !possibilities.isEmpty) {
              //interpreted but application has wrong arity
              (TypingFailure(ap + " has the wrong arity"), TrivialCstr)
            } else {
              //case cls
              val (argsTR, argsCstr) = (args map processE).unzip
              val caseTpe = symbolToType.getOrElseUpdate(ap.symbol, CaseType(fct, args.map(_ => Type.freshTypeVar)))
              if (argsTR forall (_.success)) {
                val argsTyped = argsTR map (_.get)
                val caseType = CaseType(fct, argsTyped.map(_.tpe))
                val typed = Application(fct, argsTyped) setType caseType setSymbol ap.symbol
                (TypingSuccess(typed), ConjCstr(SingleCstr(caseType, caseTpe) :: argsCstr))
              } else {
                (argsTR.find(r => !r.success).get, TrivialCstr)
              }
            }
        }
    }

    val (tpe, cstrs) = (actors map processA).unzip
    if (tpe forall (_.success)) {
      (TypingSuccess(tpe map (_.get)), ConjCstr(cstrs.toList))
    } else {
      (tpe.find(r => !r.success).get.error, TrivialCstr)
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
