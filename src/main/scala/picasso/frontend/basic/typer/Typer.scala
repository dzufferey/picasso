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

  //returns a typed formula (with error, wildcards in case of failure)
  //The boolean indicates whether the formula was typed
  /*
  def apply(e: Expression): TypingResult[Expression] = {
    //(1) scope and symbols of the Expression
    //Console.println("starting to type " + e)
    assignSymbols(e)
    //Console.println("symbol assigned")
    //(2) extract type equations
    val (tvarToSymbol, e2, eqs) = extractEquations(e)
    if (e2.success) {
      //(3) unifies type equations
      val eqs2 = eqs.normalize
      //Console.println("equations extracted: " + eqs)
      val solution = solveConstraints(eqs2)
      //Console.println("able to solve equations: " + solution.isDefined)
      //(4) uses the type info to resolve the overloading and replace the types
      solution.headOption match {
        case Some(subst) => putTypes(e2.get, tvarToSymbol, subst)
        case None => TypingFailure("cannot solve: " + eqs2)
      }
    } else {
      e2 
    }
  }
  */

  def assignSymbolsToVars(a: Actor) {
    def inScope(id: ID, scope: Map[String, Symbol]) {
        assert(scope contains id.id)
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
    

  def extractEquations(actors: Seq[Actor]): (Map[TypeVariable, Symbol], TypingResult[Seq[Actor]], TypeConstraints) = {
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
    def constraintsForActor(a: Actor): (TypingResult[Actor], TypeConstraints) = {
      //params
      val (paramsTResult, paramsCstr) = (a.params map processIdent).unzip
      val typedID = paramsTResult.map(_.get)
      //represents an actor as a fct: params -> classType ? (i.e. type of Ctor)
      symbolToType += (a.symbol -> Function(typedID map (_.tpe), ActorType(a.id, Nil)))
      //then type the body
      val (bodyTR, bodyCstr) = processPo(a.body)
      if (bodyTR.success) {
        (TypingSuccess(Actor(a.id, typedID, bodyTR.get)), ConjCstr(bodyCstr :: paramsCstr))
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
            (TypingSuccess(Send(destTR.get, contTR.get)), ConjCstr(List(destCstr, contCstr)))
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
                (TypingSuccess((srcTR.get, patTR.get, procTR.get)), ConjCstr(List(srcCstr, patCstr, procCstr)))
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
              (TypingSuccess(ITE(condTR.get, trueTR.get, falseTR.get)), ConjCstr(List(condCstr, trueCstr, falseCstr)))
            } else (falseTR, TrivialCstr)
          } else (trueTR, TrivialCstr)
        } else (condTR.error, TrivialCstr)
      case While(condition , body) =>
        val (condTR, condCstr) = processE(condition)
        val (bodyTR, bodyCstr) = processPo(body)
        if (condTR.success) {
          if (bodyTR.success) {
            (TypingSuccess(While(condTR.get, bodyTR.get)), ConjCstr(List(condCstr, bodyCstr)))
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
            val actorTpe = symbolToType.getOrElseUpdate(ap.symbol, ActorType(cls, args.map(_ => Type.freshTypeVar)))
            // ...
            sys.error("TODO")
          case _ =>
            //TODO interpreted or case
            // ...
            sys.error("TODO")
        }
    }

    sys.error("TODO")
  }

  /* TODO
  def extractEquations(e: Expression): (Map[TypeVariable, Symbol], TypingResult[Expression], TypeConstraints) = {
    var symbolToType = scala.collection.mutable.HashMap[Symbol, Type]()
    def process(e: Expression): (TypingResult[Expression], TypeConstraints) = e match {
      case a @ Application(fct, args) =>
        val possibilities = Definitions.forName(fct).filter(_.arity == args.size)
        if (possibilities.size >= 1) {
          val (args2, argsCstr) = args.map(process).unzip
          //leave symbol pending until the overloading is resolved
          (args2) find (r => !r.success) match {
            case Some(err) => (err, TrivialCstr)
            case None =>
              val unwrappedArgs = args2.map(_.get)
              val returnT = Type.freshTypeVar
              val argsTypes = unwrappedArgs.map(_.tpe)
              val a2 = Application(fct, unwrappedArgs) setType returnT
              val cases = possibilities.map( deff => {
                val (argsType, returnType) = deff.freshCopyOfType._2 match {
                  case FunctionT(a, r) => (a,r)
                  case other => (Nil, other)
                }
                val returnCstr = SingleCstr(returnT, returnType)
                val argsCstrs = argsType zip argsTypes map { case (a,b) => SingleCstr(a,b) }
                //Console.println(a + " -> " + argsCstrs + " -> " + returnCstr)
                ConjCstr(returnCstr :: argsCstrs)
              })
              val cstr = ConjCstr(argsCstr ::: List(DisjCstr(cases)))
              (TypingSuccess(a2), cstr)
          }
        } else {
          //No possible definition for fct
          (TypingFailure(a + " is not delcared or has the wrong arity"), TrivialCstr)
        }
    }
    //
    val (tpe, cstrs) = process(e)
    val typeToSymbol = symbolToType.flatMap{
      case (sym, v @ TypeVariable(_)) => List((v, sym))
      case _ => Nil
    }
    (typeToSymbol.toMap, tpe, cstrs)
  }
  */
  

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
    case _ => None
  }
  

  //TODO
  /*
  def putTypes(e: Expression, tvarToSymbol: Map[TypeVariable, Symbol], subst: Map[TypeVariable, Type]): TypingResult[Expression] = {
    //in the current version, e contains the appropriate type, so no need to check for the smbols
    def addType(e: Expression): Unit = e match {
      case l @ Literal(_) => l.tpe = l.tpe.alpha(subst)
      case v @ Variable(_) => v.tpe = v.tpe.alpha(subst)
      case a @ Application(fct, args) =>
        args foreach addType
        a.tpe = a.tpe.alpha(subst)
        //resolve the overloading if needed
        if (a.symbol == NoSymbol) {
          val actualType = FunctionT(args.map(_.tpe), a.tpe)
          Definitions.forName(fct).filter(_.arity == args.size).find( deff => unify(deff.freshCopyOfType._2, actualType).isDefined) match {
            case Some(deff) => a.symbol = deff.symbol
            case None => error("cannot resolve overloading")
          }
        }
      case Binding(_, vars, expr) =>
        addType(expr)
        vars foreach addType
    }
    try {
      addType(e)
      TypingSuccess(e)
    } catch {
      case err: java.lang.RuntimeException => TypingError(err.toString)
    }
  }
  */
}
