package picasso.frontend.compilerPlugin.backend

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin._
import scala.tools.nsc._
import picasso.ast.{Ident => PIdent, Value => PValue, Process => PProcess, Block => PBlock, _}
import picasso.utils.Namer
import picasso.math.hol.{Variable, Channel}
import picasso.graph._

/** Translation (compilation) of preprocessed (abstracted) systems into pi-calculus (or similar).
 *  Disclamer: this is going to be one of the most aweful thing I have ever done in such a project.
 *  To easily handle a lot of the complex stuctures of scala, we are going to compile a subset
 *  of the language to a pi-like-calculus. This is not a very refined and elegant way to do things,
 *  but it has the advantage of being quite general. Also it will be terrible for the verification
 *  engine that will analyze the resulting system.
 *  Morituri te salutant!
 */
trait PiCodeTranslator {
  self: AnalysisUniverse =>

  import global._

  //TODO case classes: expand when sending

  //the straight forward way of filling the offsets
  def initDispatchTables = {
    //(1) get all methods symbols of all classes (still grouped by class)
    //val symbols = for (c <- classes.values) yield c.methods.keys
    //(2) then modulo overriding
    val uniqueSymbols = new scala.collection.mutable.HashSet[Symbol]()
    for (c <- classes.values; m <- c.methods.values) {
      val unique = m.earliestSymbol
      uniqueSymbols += unique
      DispatchTable.toUnique += (m.symbol -> unique)
      DispatchTable.toUnique += (unique -> unique)
    }
    //(3) then stuff we don't have code or semantics for are replaced by something
    //this is alerady only the methods we have the code of.
    uniqueSymbols ++= List(startMethod, restartMethod)
    DispatchTable.toUnique ++=  List(startMethod -> startMethod, restartMethod -> restartMethod)
    //(4) then assign an order to that sequence
    //0 is not used, it can be used for anything we don't know about.
    var offset = 1
    for (s <- uniqueSymbols) {
      DispatchTable.offsets += (s -> offset)
      offset = offset + 1
    }
    //then map all the symbols
    for ((s,u) <- DispatchTable.toUnique) DispatchTable.offsets += (s -> DispatchTable.offsets(u))
    //then says it was initilaized
    DispatchTable.initialized = true
    //TODO compact the table get things more compact
  }

  def hasCodeFor(sym: Symbol) = {
    if (sym.isMethod) DispatchTable.toUnique contains sym //method
    else classes contains sym //class or object
  }

  /** What the function should be (argument for high order methods).
   *  Retruns either a type + ctor args, or the identifier that points to the anonfun object */
  def findFctInBlock(t: Tree): List[Tree] = t match {
    case Typed(e,_) => findFctInBlock(e)
    case Block(List(ValDef(_, _, _, Apply(Select(n @ New(fct), _), args))), _) => fct :: args
    case Ident(id) => List(t)
    case err => Logger.logAndThrow("Plugin", LogError, "PiCodeTranslator, findFctInBlock: " + err)
  }

  def actorOfType(t: Type) = idOfSymbol(t.typeSymbol)

  //TODO put the markup in its own file

  /** Store marked symbols for easy lookp.
   *  The information stored in the markup are sufficient to identify any
   *  symbol.  But the symbol can be a method, a value, a clazz, so the lookup
   *  can be tricky.
   */
  val markedSymbol = new scala.collection.mutable.HashMap[Int, Symbol]

  val markupPrefix = "@TODO@"
  val markupSep = "@"
  
  def markupSym(about: String, syms: Symbol*): String = {
    Logger("Plugin", LogDebug, "PiCodeTranslator, markup: " + about + " -> " + syms)
    for (s <- syms) markedSymbol += (s.id -> s)
    markupPrefix + about + markupSep + syms.map(s => idOfSymbol(s)).mkString("",markupSep,"")
  }

  def markup(about: String, t: Tree*): String = markupSym(about, t.map(_.symbol):_*)

  def isMarkup(str: String): Option[List[String]] = {
    if (str.startsWith(markupPrefix)) {
      val suffix = str.substring(markupPrefix.length)
      Some(suffix.split(markupSep).toList)
    } else None
  }
  
  /** return what a marked stuff contains */
  def isMarkupSym(str: String): Option[(String, List[Symbol])] = {
    if (str.startsWith(markupPrefix)) {
      val suffix = str.substring(markupPrefix.length)
      val splitted = suffix.split(markupSep).toList
      val what = splitted.head
      val symsStr = splitted.tail
      val ids = for (str <- symsStr) yield str.split("#")(1).toInt
      val syms = ids map (markedSymbol(_))
      Some((what, syms))
    } else None
  }
  
  def patternOfTree(t: Tree): Pattern = t match {
    case bd @ Bind(name, t2) => Binding(IDOfSymbol(bd.symbol), patternOfTree(t2))
    case Apply(id, args) => Case(id.symbol.name.toString, args map patternOfTree)
    case Ident(id) => Case(id.toString, Nil)
    case err => Logger.logAndThrow("Plugin", LogError, "PiCodeTranslator, patternOfTree: " + err)
  }
  
  def makeFctCall(  pre: List[PProcess],
                    callee: Expression,
                    toCall: Symbol, 
                    args: List[Expression],
                    returnPat: Pattern,
                    post: List[PProcess] ): PBlock = {
    val toCallStr = idOfSymbol(DispatchTable.symbolToCall(toCall))
    val retChan = ID(Variable("returnLocal") setType Channel())
    val body = List(
      Affect(retChan, NewChannel()), //create a new channel for the return
      Send(callee, Application(toCallStr, retChan :: args)), //send the appropriate message
      Receive(retChan, returnPat) //wait for the reply (affect by the way)
    )
    PBlock(pre ::: body ::: post)
  }

  def makeFctCall(  pre: List[PProcess],
                    callee: Either[Tree,Expression],
                    toCall: Symbol, 
                    args: List[Tree],
                    returnVal: Option[Symbol],
                    post: List[PProcess] ): PProcess = {
    val callee2 = callee match {
      case Left(callee) => expressionOfTree(callee)
      case Right(expr) => expr
    }
    val returnPat = returnVal.map(s => PIdent(IDOfSymbol(s))).getOrElse(Wildcard)
    makeFctCall(pre, callee2, toCall, args.map(expressionOfTree), returnPat, post)
  }

  object ExpressionOfTreeOperations {
    def unapply(t: Tree): Option[Expression] = {
      operations.find(o => o.expression.isDefinedAt(t)).map(_.expression(t))
    }
  }

  def expressionOfTree(t: Tree): Expression = t match {
    case ExpressionOfTreeOperations(expr) => expr
    case ExAssert(tree) => Application("assert", List(expressionOfTree(tree)))
    case ExAssume(tree) => Application("assume", List(expressionOfTree(tree)))
    case ExEquals(t1, t2) => Application("==", List(expressionOfTree(t1), expressionOfTree(t2)) )
    case ExNotEquals(t1, t2) => Application("!=", List(expressionOfTree(t1), expressionOfTree(t2)) )
    case ExWrapper(wrapped) => expressionOfTree(wrapped)
    case Select(_, _) | Ident(_)  => IDOfSymbol(t.symbol)
    case This(_) => thisChannel
    case Literal(Constant(any)) => PValue(StringVal(any.toString))
    case err => Logger("Plugin", LogWarning, "PiCodeTranslator: dropping " + headString(err) + " " + err); Any
  }

  object ProcessOfTreeOperations {
    def unapply(t: Tree): Option[PProcess] = {
      operations.find(o => o.process.isDefinedAt(t)).map(_.process(t))
    }
  }

  def processOfTree(t: Tree): PProcess = t match {
    //TODO pattern somewhere else ??
    case MatchCase(matching, pattern) => Receive(expressionOfTree(matching), patternOfTree(pattern)) //not the right way but will do for the moment
    case cd @ CaseDef(_,_,_) => Logger("Plugin", LogWarning, "PiCodeTranslator: dropping CaseDef " + cd); Zero()

    case ProcessOfTreeOperations(ops) => ops

    //object creation (if we know what kind of object it is)
    case ExObjectNew(tpt, args) if hasCodeFor(tpt.typeSymbol) =>
      val tmp = ID(Variable("tmp") setType typeOfSymbol(tpt.typeSymbol)) //TODO is that right
      val pre = List(Affect(tmp, Create(actorOfType(tpt), List(NewChannel()))))
      makeFctCall(pre, Right(tmp), tpt.typeSymbol.primaryConstructor, args, None, Nil)
    case Assign(lhs, ExObjectNew(tpt, args)) if hasCodeFor(tpt.typeSymbol) =>
      val pre = List(Affect( IDOfSymbol(lhs.symbol), Create(actorOfType(tpt), List(NewChannel()))))
      makeFctCall(pre, Left(lhs), tpt.typeSymbol.primaryConstructor, args, None, Nil)

    //function call (TODO if the call is tail, then can put retrun as callee's return an directly finishes)
    case Assign(lhs, Apply(fct @ Select(obj, name), args)) if (hasCodeFor(fct.symbol)) =>
      makeFctCall(Nil, Left(obj), fct.symbol, args, Some(lhs.symbol), Nil)
    case Apply(fct @ Select(obj, name), args) if (hasCodeFor(fct.symbol)) =>
      makeFctCall(Nil, Left(obj), fct.symbol, args, None, Nil)

    //rest
    case Assign(lhs, rhs) => Affect(IDOfSymbol(lhs.symbol), expressionOfTree(rhs))
    case EmptyTree => Skip()
    case t: TermTree => Expr(expressionOfTree(t))
    case t: RefTree => Expr(expressionOfTree(t))
    case err => Logger.logAndThrow("Plugin", LogError, "PiCodeTranslator, processOfTree: " + err)
  }

  //how actors are created:
  //new: create a new agent waiting for a start message
  //(re)start: send a start message
  //exit: go in wait for start mode

  def marked[A](agt: AgentDefinition[A]): List[(A,(String, List[Symbol]),A)] = {
    val opts = agt.cfa.edges.map{
       case (a, Expr(PValue(StringVal(p))), b) =>  isMarkupSym(p).map((a, _, b))
       case _ => None
    }
    opts.flatMap(_.toList).toList
  }

  /* Remove the marking using the defined operations */
  def removeMarking(agt: AgentDefinition[PC]) : Option[AgentDefinition[PC]] = {
    var changed = false
    val newAgt = (agt /: operations)( (agt, op) => {
      val chgt = op.removeMarking(agt)
      if (chgt.isDefined) changed = true
      chgt getOrElse agt
    })
    if (changed) Some(newAgt) else None
  }

  def ctorAssigns(a: AgentDefinition[PC]): List[(ID,ID)] = {
    a.cfa.edges.flatMap{
      case (_, Affect(v1, v2 @ ID(_)) ,_) => List(v1 -> v2)
      case _ => Nil
    }.toList
  }

  /** a method in an agetn created with the following args (ctor inlined/ substitution) */
  def createdAgentWithArgs(clazz: Symbol, method: Name, args: List[ID]): AgentDefinition[PC] = {
    val rcvFct = PClasses(clazz).methodAgent(method)
    val ctor =  PClasses(clazz).methodAgent(nme.CONSTRUCTOR)
    val partialSubst1 = ctor.params.drop(2) zip args
    val partialSubst2 = ctorAssigns(ctor)
    val partialSubst  = partialSubst2 map { case (orig, inter) =>
      val res = partialSubst1.find(_._1 == inter).map(_._2).getOrElse(inter)
      (orig, res)
    }
    val (lhs, rhs) = partialSubst.unzip
    instanciateArgsID(rcvFct, lhs, rhs)
  }

  //TODO fancy things happening here -> type symbols in markings ...

  //TODO change the way fct + args are fetched ...
  def findObjectCreation(a: AgentDefinition[PC], syms: List[Symbol]): (Symbol, List[ID], AgentDefinition[PC]) = {
    //Logger("Plugin", LogDebug, "PiCodeTranslator: findObjectCreation for " + a.id + syms.map(IDOfSymbol).mkString("(", ",", ")"))
    val classSymOrIdent = syms.head
    val args = syms.tail
    if (classSymOrIdent.isType) {
      (classSymOrIdent, args map IDOfSymbol, a)//easy case, we already have everything.
    } else {
      assert(classSymOrIdent.isTerm && args.isEmpty)
      val idTolookFor = IDOfSymbol(classSymOrIdent)
      //TODO at that point everything is in the same block
      //Console.println("looking for " + idTolookFor)
      //Console.println(a.toString)
      val matchingEdges = a.cfa.edges.flatMap{case (a, blk @ PBlock(Affect(`idTolookFor`, Create(tpe, _)) :: rest),b) => List((a,tpe, rest, blk,b)); case _ => Nil}
      assert(matchingEdges.size == 1, "matchingEdges.size == " + matchingEdges.size)
      //the fct call is new return symbol, send, receive.
      val (loc1, tpe, rest, blk, loc2) = matchingEdges.head
      assert(rest.size == 3)
      //returnLocal
      val newChan = rest(0)
      //send <init>
      val sendInit = rest(1)
      //returnLocal ?
      val receiveReturn = rest(2)
      //make a skip edge to replace the object creation
      val a2Cfa = a.cfa - (loc1,blk,loc2) + (loc1, Skip(), loc2)
      val a2 = new AgentDefinition(a.id, a.params, a2Cfa)
      //get the args
      val argsRaw = sendInit match {
        case Send(_, Application(_, retChan :: args)) => args
        case err => Logger.logAndThrow("Plugin", LogError, "PiCodeTranslator: cannot find args in " + err)
      }
      val argsID = argsRaw.map{
        case id @ ID(_) => id
        case err => Logger.logAndThrow("Plugin", LogError, "PiCodeTranslator: arg is not ID: " + err)
      }
      //get the type
      val clazz = PClasses.keys.find(x => idOfSymbol(x) == tpe).get
      (clazz, argsID, a2)
    }
  }

  /** passing high-order arguments: returns the object (reference) that contains the method and the method symbol. */
  def findCalleeAndMethod(a: AgentDefinition[PC], ref: Symbol): (ID, Symbol) = {
    if (ref.isMethod) {
      sys.error("TODO: ref is already a method")
    } else {
      val symApply =  ref.info.decl(nme.apply)
      (IDOfSymbol(ref), symApply)
    }
  }

  
  /** Retrurns a new agent where the parameters have been instanciated by the given list. */
  def instanciateArgsID[PC](a: AgentDefinition[PC], ctorArgs: List[ID], args: List[ID]): AgentDefinition[PC] = {
    Logger("Plugin", LogDebug, "instanciateArgsID replacing: " + ctorArgs + " by " + args + " in " + a.id)
    assert(ctorArgs.length == args.length)
    val map = Map[Expression, Expression]((ctorArgs zip args):_*)
    val a2 = a.morphFull((x:PC) => x, p => substExprP(p, map))
    new AgentDefinition[PC](a.id, a.params, a2.cfa)
  }

  def instanciateArgs(a: AgentDefinition[PC], ctorArgs: List[ID], args: List[Symbol]): AgentDefinition[PC] = {
    val pargs = args.map(s => if (s.isThisSym) thisChannel else IDOfSymbol(s))
    instanciateArgsID(a, ctorArgs, pargs)
  }

  /** For react and receive inlinning, the first receive is for a message, and needs to be unpacked */
  def unpackMsg[PC](a: AgentDefinition[PC]): AgentDefinition[PC] = {
     val edgesToChange = a.cfa.adjacencyMap(a.cfa.initState)
     assert(edgesToChange.keys.forall{
       case Receive(_,_) => true
       case _ => false
     })
     val newEdges = edgesToChange.map{ case (k,v) => k match {
       case Receive(from,pat) => (Receive(from, unpackMessageWithSender(pat)), v)
       case k => (k,v)
     }}
     val newMap = a.cfa.adjacencyMap + (a.cfa.initState -> newEdges)
     new AgentDefinition(a.id, a.params, newMap, a.cfa.initState, a.cfa.targetStates)
  }
  
  /** replace refrences to the class itself by this */
  def thisify[PC](clazz: Symbol, a: AgentDefinition[PC]): AgentDefinition[PC] = {
    Logger("Plugin", LogDebug, "thisify: " + clazz + " -> " + a)
    val id = IDOfSymbol(clazz)
    instanciateArgsID(a, List(id), List(thisChannel))
  }

  def substExprP(p: PProcess, map: Map[Expression, Expression]): PProcess = p match {
    case PBlock(stmts) => PBlock(stmts map (substExprP(_, map)))
    case Affect(id, v) => Affect(id, substExprE(v, map))
    case Expr(e: Expression) => Expr( substExprE(e, map))
    case Send(dest: Expression, content: Expression) => Send(substExprE(dest, map), substExprE(content, map))
    case Receive(src: Expression, pat: Pattern) => Receive(substExprE(src, map), pat)
  }
 
  def substExprE(e: Expression,  map: Map[Expression, Expression]): Expression = e match {
    case ap @ Application(fct, args) => map.get(ap).getOrElse(Application(fct, args.map(substExprE(_,map))))
    case t @ Tuple(values) => map.get(t).getOrElse(Tuple(values.map(substExprE(_,map))))
    case other => map.getOrElse(other,other)
  }

  def substPat(p: Pattern, map: Map[Pattern, Pattern]): Pattern = p match {
    case p @ PatternTuple(lst) => map.get(p).getOrElse(PatternTuple(lst.map(substPat(_,map))))
    case c @ Case(uid, args) => map.get(c).getOrElse(Case(uid, args.map(substPat(_,map))))
    case other => map.getOrElse(other,other)
  }


  def edgeForGetter[PC](getter: AgentDefinition[PC]): PProcess = {
    val edge = getter.cfa.edges.filter{case (a,_,_) => a == getter.cfa.initState}
    assert(edge.size == 1)
    val retID = ID(retVar)
    edge.head match {
      case (_, Affect(_, id),_) => Send(retID, id)
      case (_, Send(`retID`, Any), _) => Send(retID, Any)
      case (_, what_?,_) => Logger.logAndThrow("Plugin", LogError, "" + what_?)
    }
  }

  def createEdge[PC](tbl: AgentDefinition[PC], method: String): (PC, PProcess, PC) = {
    val edge = tbl.cfa.edges.filter{
      case (_, Expr(Create(`method`, _)), _) => true
      case _ => false
    }
    assert(edge.size == 1, "edge = " + edge + " in " + tbl.cfa.edges)
    edge.head
  }

  /** merge the getter, setters and primary constructor into the object
   *  TODO  ctor of super class should be inlined into the current ctor (ctor cannot call a fct of "this")
   *        this is actually quite restrictive, so the calls should be treated as call ?
   */
  def mergeGettersSettersCtorIntoDispatch(tbl: DispatchTable,
                                          ctor: MethodExecutor,
                                          getters: List[MethodExecutor],
                                          setters: List[MethodExecutor]) = {
    /* check that there is no call to this or inline them again ? */
    def prepareCtor(ctor: AgentDefinition[PC]): AgentDefinition[PC] = {
      //TODO ...
      ctor
    }
    def inlineCtor(tbl: AgentDefinition[PC], _ctor: AgentDefinition[PC]): AgentDefinition[PC] = {
      val ctor = prepareCtor(_ctor)
      val edge = createEdge(tbl, ctor.id)
      val n1 = ctor.cfa.initState
      val n2 = ctor.cfa.targetStates.head
      val cfa2 = tbl.cfa.replaceEdgeBy(edge, ctor.cfa, n1, n2)
      new AgentDefinition(tbl.id, tbl.params, cfa2)
    }
    def inlineSetter(tbl: AgentDefinition[PC], setter: AgentDefinition[PC]): AgentDefinition[PC] = {
      inlineCtor(tbl, setter)//nothing fancy to do
    }
    def inlineGetter(tbl: AgentDefinition[PC], getter: AgentDefinition[PC]): AgentDefinition[PC] = {
      val (e1,e2,e3) = createEdge(tbl, getter.id)
      val cfa2 = tbl.cfa.-(e1, e2, e3).+(e1, edgeForGetter(getter), e3)
      new AgentDefinition(tbl.id, tbl.params, cfa2)
    }
    val tbl1 = inlineCtor(tbl.agent, ctor.agent)
    val tbl2 = (tbl1 /: getters.map(_.agent))(inlineGetter)
    val tbl3 = (tbl2 /: setters.map(_.agent))(inlineSetter)
    tbl.agent = tbl3
    val toAdd = (ctor :: getters ::: setters).map(_.method)
    tbl.includedMethod = toAdd ::: tbl.includedMethod
  }

  /** When PBloc are on the edges, unroll them */
  def unrollBlock(agt: AgentDefinition[PC]): AgentDefinition[PC] = {
    val cfa2 = (agt.cfa /: agt.cfa.edges){
      case (acc, (a, PBlock(lst), b)) =>
        val (edgesFreshOnly, _) = ((Nil: List[(PC,PProcess,PC)], a) /: lst){ case ((acc,loc), proc) =>
          val loc2 = Namer(agt.id + "$unroll")
          ((loc, proc, loc2) :: acc, loc2)
        }
        val edges = edgesFreshOnly match {
          case (l,p,_) :: xs => (l,p,b) :: xs
          case Nil => List((a, PBlock(lst), b))
        }
        acc - (a, PBlock(lst), b) ++ edges
      case (acc, _) => acc
    }
    new AgentDefinition(agt.id, agt.params, cfa2)
  }

  def makeAllCombination[A](lst: List[A]): List[Map[A,Boolean]] = lst match {
    case x::xs => makeAllCombination(xs).flatMap( map => List(map + (x -> true), map + (x -> false)))
    case Nil => List(Map.empty[A,Boolean])
  }

  def newLoc(oldLoc: PC, valuation: Map[Variable,Boolean]): PC = {
    def b2c(b: Boolean) = if (b) 't' else 'f'
    val sequence = valuation.keys.toSeq.sortWith((v1, v2) => v1.name < v2.name).map(x => b2c(valuation(x)))
    oldLoc + sequence.mkString("","","")
  }

  def frameOk(pre: Map[Variable, Boolean], p: PProcess, post: Map[Variable, Boolean]) = {
    val toCheck = pre -- p.writtenIDs.map(_.id)
    toCheck.keys forall (s => !(post contains s) || pre(s) == post(s))
  }

  def affectOk(pre: Map[Variable, Boolean], p: PProcess, post: Map[Variable, Boolean]) = p match {
    case PBlock(Nil) => true
    case PBlock(stmts) => Logger.logAndThrow("Plugin", LogError, "affectOk cannot deal with Block")//stmts forall (satisfiable(pre,_,post))
    case Affect(ID(id), v) if post contains id => evaluate(pre, v) map (_ == post(id)) getOrElse true
    case Assume(e) =>
      evaluate(pre, e) match {
        case Some(true) => true
        case Some(false) =>
          Logger("Plugin", LogWarning, "Assume(false) removing edge")
          false
        case None =>
          Logger("Plugin", LogWarning, "Assume(?) ignoring")
          true
      }
    case Assert(e) =>
      evaluate(pre, e) match {
        case Some(true) => true
        case Some(false) =>
          Logger("Plugin", LogWarning, "Assert(false) this should be marked as an error, now ignoring")
          true
        case None => 
          Logger("Plugin", LogWarning, "Assert(?) this should be marked as a potential error, now ignoring")
          true
      }
    case Affect(_, _) | Expr(_) | Send(_, _) | Receive(_, _) => true
  }

  /** very weak version of {pre}p{post} (exists instead of forall) */
  def satisfiable(pre: Map[Variable, Boolean], p: PProcess, post: Map[Variable, Boolean]): Boolean =
    frameOk(pre, p, post) && affectOk(pre, p, post)

  /** Evalutates ground boolean expression */
  def ev(e: Expression): Option[Boolean] = e match {
    case PValue(Bool(b)) => Some(b)
    case Application("&&", lst) =>
      val evaluated = lst map ev
      if (evaluated exists (_ == Some(false))) Some(false)
      else if (evaluated exists (_.isEmpty)) None
      else Some(true)
    case Application("||", lst) =>
      val evaluated = lst map ev
      if (evaluated exists (_ == Some(true))) Some(true)
      else if (evaluated exists (_.isEmpty)) None
      else Some(false)
    case Application("^", List(e1,e2)) =>
      ev(e1).flatMap(b1 => ev(e2).map(b2 => b1 ^ b2))
    case Application("!", List(e)) => ev(e).map(!_)
    case Application("==", List(e1,e2)) if (e1 == e2) => Some(true)
    case Application("==", List(PValue(a),PValue(b))) => Some(a == b)
    case Application("==", List(e1,e2)) => ev(e1) flatMap (b1 => ev(e2) map (_ == b1))
    case Application("!=", args) => ev(Application("!",List(Application("==", args))))
    case _ => None
  }

  def evaluate(pre: Map[Variable, Boolean], e: Expression): Option[Boolean] = {
    val map: Map[Expression, Expression] = pre.map{case (k,v) => (ID(k), PValue(Bool(v)))}
    ev(substExprE(e, map))
  }

  def simplifyKnownMethod(e: Expression): Expression = e match {
    case b if ev(b).isDefined => PValue(Bool(ev(b).get))
    case Application(fct, args) => Application(fct, args map simplifyKnownMethod)
    case other => other
  }

  /** Substitute values depending on the current state. */
  def instanciate(pre: Map[Variable, Boolean], p: PProcess, post: Map[Variable, Boolean]): PProcess = {
    val map: Map[Expression, Expression] = pre.map{case (k,v) => (ID(k), PValue(Bool(v)))}
    val mapPat: Map[Pattern, Pattern] = post.map{case (k,v) => (PIdent(ID(k)), PatternLit(Bool(v)))}
    def pp(p: PProcess): PProcess = p match {
      case PBlock(stmts) => PBlock(stmts map pp)
      case Affect(id, v) => Affect(id, simplifyKnownMethod(substExprE(v, map)))
      case a @ Assume(e) =>
        evaluate(pre, e) match {
          case Some(b) => Assume(PValue(Bool(b)))
          case None => a
        }
      case a @ Assert(e) =>
        evaluate(pre, e) match {
          case Some(b) => Assert(PValue(Bool(b)))
          case None => a
        }
      case Expr(e) => Expr(simplifyKnownMethod(substExprE(e, map)))
      case Send(dest, content) => Send(dest, simplifyKnownMethod(substExprE(content, map)))
      case Receive(src, pat) => Receive(src, substPat(pat, mapPat))
    }
    pp(p)
  }
  
  /** make an assume for assigned each variable in the store */
  def initAssume(post: Map[ID, Boolean]): PProcess = {
    val expr = post.iterator.map{case (id,b) => if(b) id else Application("!", List(id))}.toList
    Assume(Application("&&", expr))
  }

  def expandBooleanVariables(syms: Iterable[Symbol], agt: AgentDefinition[PC]) = {
    assert(syms forall (isBoolean(_)))
    val lives = liveVariablesRestrictedTo(syms, agt)
    //state to all possible boolean store
    val possibleStates = lives.mapValues(vars => makeAllCombination(vars.toList))
    //need to take the 'product' with the cfa (with only transition that can happens)
    val newEdges = agt.cfa.edges.flatMap{ case (a, proc, b) =>
      val possibleStatesVarA = possibleStates(a).map(_.map{case (ID(id),v) => (id,v)})
      val possibleStatesVarB = possibleStates(b).map(_.map{case (ID(id),v) => (id,v)})
      for (pre <- possibleStatesVarA;
           post <- possibleStatesVarB
           if satisfiable(pre, proc, post))
      yield (newLoc(a,pre), instanciate(pre, proc, post), newLoc(b,post))
    }
    //when there are multiple initate, we need to add some assume (new init with one transition to each actual init)
    val (newInit, initEdges) = if (possibleStates(agt.cfa.initState).size > 1) {
      val init2 = Namer(agt.cfa.initState)
      val edges = for(conf <- possibleStates(agt.cfa.initState)) yield (init2, initAssume(conf), newLoc(agt.cfa.initState, conf.map{case (ID(id),v) => (id,v)}))
      (init2, edges)
    } else (agt.cfa.initState, Nil)
    val newTarget = agt.cfa.targetStates.flatMap( v => possibleStates(v).map(conf => newLoc(v,conf.map{case (ID(id),v) => (id,v)})))
    val newAutomaton = Automaton[GT.ELGT{type V = PC; type EL = PProcess}](initEdges ++ newEdges, newInit, newTarget)
    //remove dead code: expansion creates states without incoming state.
    new AgentDefinition[PC](agt.id, agt.params, newAutomaton.removeUnreachableStates)
  }
  
  def expandBooleanVariablesMethod(m: MethodExecutor) = {
    //variables of included methods should have been removed, so it should be fine
    val booleanVars = m.localVariables.filter(isBoolean(_))
    m.agent = expandBooleanVariables(booleanVars, m.agent)
  }

  def expandBooleanVariablesClass(tbl: DispatchTable) = {
    val booleanVars = tbl.localVariables.filter(isBoolean(_))
    tbl.agent = expandBooleanVariables(booleanVars, tbl.agent)
  }

}
