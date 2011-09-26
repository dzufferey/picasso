package picasso.frontend.compilerPlugin

import scala.tools.nsc.Global

trait Extractors {
  self: Definitions =>

  val global: Global
  import global._
  import global.definitions._


  //big parts of this file come from Funcheck
  //TODO: speak with Philippe about having a common infrastructure (which is tricky due to the Global).

  object ScalaPredef {
    /** Extracts method calls from scala.Predef. */
    def unapply(tree: Select): Option[Symbol] = tree match {
      case select @ Select(predef, name) if predef.symbol == PredefModule =>
        assert(select.hasSymbol)
        Some(select.symbol) 
      case _ => None
    }
    def apply(s: Symbol) = Select(This(PredefModule), s)
  }

  object ExAssert {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(ScalaPredef(sym), arg :: Nil) if isAssert(sym) => Some(arg)
      case _ => None
    }
    def apply(cond: Tree) = {
      assert(cond.tpe =:= BooleanClass.tpe)
      treeCopy.Apply(cond, ScalaPredef(predefAssert1), List(cond)) setType UnitClass.tpe
    }
  }

  object ExAssume {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(ScalaPredef(sym), arg :: Nil) if isAssume(sym) => Some(arg)
      case _ => None
    }
    def apply(cond: Tree) = {
      assert(cond.tpe =:= BooleanClass.tpe)
      treeCopy.Apply(cond, ScalaPredef(predefAssume1), List(cond)) setType UnitClass.tpe
    }
  }

  //TODO test
  object ExEnsuring {
    def unapply(tree: Apply): Option[(Tree, Tree)] = tree match {
      case Apply(s2 @ Select(Apply(TypeApply(s1 @ Select(_,_), _), body::Nil), _), ensure::Nil)
        if s1.symbol == predefAny2Ensuring && s2.symbol == predefEnsuringEnsuring => Some((ensure,body))
      case _ => None
    }
    def apply(ensure: Tree, body: Tree) = {
      val s1 = Select(This(PredefModule), predefAny2Ensuring)
      val tp = TypeApply(s1, List(TypeTree(body.tpe)) )
      val ap = Apply(tp, List(body))
      val s2 = Select(ap, predefEnsuringEnsuring)
      val req = Apply(s2, List(ensure))
      //TODO type ?
      req
    }
  }

  object ExRequire {
    def unapply(tree: Block): Option[(Tree,Tree)] = tree match {
      case Block(Apply(ScalaPredef(sym), arg :: Nil) :: rest, e) if sym == predefRequire1 =>
        Some((arg, if (rest.isEmpty) e else Block(rest, e)))
      case _ => None
    }
    def apply(require: Tree, body: Tree) = {
      val req = Apply(Select(This(PredefModule), predefRequire1), List(require))
      body match {
        case Block(es, e) => Block(req :: es, e) setType body.tpe
        case b => Block(List(req), b) setType body.tpe
      }
    }
  }

  /////////
  //Boolean
  /////////

  object ExBooleanLiteral {
    def unapply(tree: Literal): Option[Boolean] = tree match {
      case Literal(Constant(true)) => Some(true)
      case Literal(Constant(false)) => Some(false)
      case _ => None
    }
  }
  object ExAnd {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_and) => Some((lhs,rhs))
      case _ => None
    }
    def apply(t1: Tree, t2: Tree) = {
      assert(t1.tpe =:= BooleanClass.tpe && t2.tpe =:= BooleanClass.tpe)
      Apply(Select(t1, Boolean_and), List(t2)) setType BooleanClass.tpe
    }
  }
  
  object ExOr {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_or) => Some((lhs,rhs))
      case _ => None
    }
    def apply(t1: Tree, t2: Tree) = {
      assert(t1.tpe =:= BooleanClass.tpe && t2.tpe =:= BooleanClass.tpe)
      Apply(Select(t1, Boolean_or), List(t2)) setType BooleanClass.tpe
    }
  }
  
  object ExXor {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_xor) => Some((lhs,rhs))
      case _ => None
    }
  }
  
  //TODO with symbol
  object ExNot {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(Select(t, n), Nil) if n == nme.UNARY_! => Some(t)
      case _ => None
    }
    def apply(cond: Tree) = {
      assert(cond.tpe =:= BooleanClass.tpe)
      val unaryNotSym = getMember(BooleanClass, nme.UNARY_!)
      treeCopy.Apply(cond, Select(cond, unaryNotSym), Nil) setType BooleanClass.tpe
    }
  }
  
  //TODO with symbol
  object ExEquals {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if n == nme.EQ => Some((lhs,rhs))
      case _ => None
    }
  }
  
  //TODO with symbol
  object ExNotEquals {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(Select(lhs, n), List(rhs)) if n == nme.NE => Some((lhs,rhs))
      case _ => None
    }
  }

  ///////
  //Actor
  ///////

  //message related

  object ExActorSend {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if checkForActorMethod(bang, s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExActorSendWithReturn {
    def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs, ret)) if checkForActorMethod(send, s.symbol) => Some((lhs,rhs,ret))
      case _ => None
    }
  }

  object ExActorSendFuture {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if checkForActorMethod(bangBang, s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }
  
  object ExActorSendSync {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if checkForActorMethod(bangQmark, s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  //TODO does not match ?
  object ExActorQmark {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(s @ Select(lhs, _), Nil) if checkForActorMethod(qmark, s.symbol) => Some(lhs)
      case _ => None
    }
  }

  object ExActorReceive {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(TypeApply(s @ Select(lhs, _), _), List(rhs)) if s.symbol == getMember(actorClass, receive) => Some((lhs,rhs))
      case _ => None
    }
  }
  
  object ExActorReceiveWithin {
    def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
      case Apply(TypeApply(s @ Select(lhs, _), _), List(timeout,rhs)) if s.symbol == getMember(actorClass, receiveWithin) => Some((lhs,timeout,rhs))
      case _ => None
    }
  }

  object ExActorReact {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if s.symbol == getMember(actorClass, react) => Some((lhs,rhs))
      case _ => None
    }
  }
  
  object ExActorReactWithing {
    def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(timeout,rhs)) if s.symbol == getMember(actorClass, reactWithin) => Some((lhs,timeout,rhs))
      case _ => None
    }
  }
  
  object ExActorSender {
    def unapply(tree: Apply): Option[(Tree)] = tree match {
      case Apply(s @ Select(lhs, _), Nil) if checkForActorMethod(sender, s.symbol) => Some(lhs)
      case _ => None
    }
  }

  object ExActorReply {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if checkForActorMethod(reply, s.symbol) => Some(lhs,rhs)
      case _ => None
    }
  }

  //control flow related
  
  object ExActorLoop {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if checkForActorMethod(loop, s.symbol) => Some((lhs,rhs))
      case Apply(s @ Select(lhs, _), List(rhs)) if isActorLoop(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }
  
  object ExActorLoopWhile {
    def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(cond,rhs)) if checkForActorMethod(loopWhile, s.symbol) => Some((lhs,cond,rhs))
      case Apply(s @ Select(lhs, _), List(cond,rhs)) if isActorLoopWhile(s.symbol) => Some((lhs,cond,rhs))
      case _ => None
    }
  }

  //creation related

  object ExObjectNew {
    def unapply(tree: Apply): Option[(Type, List[Tree])] = tree match {
      case Apply(Select(New(tpt), n), args) if (n == nme.CONSTRUCTOR) => Some((tpt.tpe, args))
      case _ => None
    }
  }

  object ExActorNew {
    def unapply(tree: Apply): Option[(Type, List[Tree])] = tree match {
      case Apply(Select(New(tpt), n), args) if (n == nme.CONSTRUCTOR && isActorClass(tpt.tpe)) => Some((tpt.tpe, args))
      case _ => None
    }
  }

  object ExActorAct {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(s @ Select(lhs, _), Nil) if checkForActorMethod(act, s.symbol) => Some(lhs)
      case _ => None
    }
  }
  
  object ExActorStart {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(s @ Select(lhs, _), Nil) if checkForActorMethod(start, s.symbol) => Some(lhs)
      case _ => None
    }
  }
  
  object ExActorRestart {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(s @ Select(lhs, _), Nil) if checkForActorMethod(restart, s.symbol) => Some(lhs)
      case _ => None
    }
  }
  
  object ExActorExit {
    def unapply(tree: Apply): Option[(Tree,Option[Tree])] = tree match {
      case Apply(s @ Select(lhs, _), Nil) if checkForActorMethod(exit, s.symbol) => Some((lhs,None))
      case Apply(s @ Select(lhs, _), List(rhs)) if checkForActorMethod(exit, s.symbol) => Some((lhs,Some(rhs)))
      case _ => None
    }
  }
  
  /*
  case ExActorSend(to, msg) =>
  case ExActorSendWithReturn(to, msg, replyTo) =>
  case ExActorSendFuture(to, msg) =>
  case ExActorSendSync(to, msg) =>
  case ExActorQmark(this) =>
  case ExActorReceive(this, fct) =>
  case ExActorReceiveWithin(this, timeout, fct) =>
  case ExActorReact(this, fct) =>
  case ExActorReactWithing(this, timeout, fct) =>
  case ExActorSender(this) =>
  case ExActorReply(this, msg) =>

  case ExActorLoop(this, fct) =>
  case ExActorLoopWhile(this, cond, fct) =>
  case ExActorNew(tpt, args) =>
  case ExActorAct(this) =>
  case ExActorStart(this) =>
  case ExActorRestart(this) =>
  case ExActorExit(this, status) =>
  */
  
  ////////////
  //Collection
  ////////////

  //a few methods micht have more arguments because of the implicit canBuildFrom, and also a TypeApply

  object ExCollectionNew {
    def unapply(tree: Tree): Option[(Type, List[Tree])] = tree match {
      case Apply(TypeApply(Select(New(tpt), n), _), args) if (n == nme.CONSTRUCTOR && isStdCollection(tpt.tpe)) => Some((tpt.tpe, args))
      case Apply(Select(New(tpt), n), args) if (n == nme.CONSTRUCTOR && isStdCollection(tpt.tpe)) => Some((tpt.tpe, args))
      case s @ Select(_, _) if (s.symbol == NilModule) => Some((ListClass.tpe, Nil))
      case Apply(TypeApply(s @ Select(comp,_), _), Nil) if isStdCollectionCompanionEmpty(s.symbol) => Some((comp.symbol.companionClass.tpe, Nil))
      case Apply(TypeApply(s @ Select(comp,_), _), args) if isStdCollectionCompanionApply(s.symbol) => Some((comp.symbol.companionClass.tpe, args))
      case _ => None
    }
  }
  
  object ExCollectionIsEmpty {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(s @ Select(lhs, _), Nil) if isStdCollectionIsEmpty(s.symbol) => Some(lhs)
      case _ => None
    }
  }

  //iteration: foreach, map, fold?, reduce?

  object ExCollectionForeach {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionForeach(s.symbol) => Some((lhs,rhs))
      case Apply(TypeApply(s @ Select(lhs, _), _), List(rhs)) if isStdCollectionForeach(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionMap {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(TypeApply(s @ Select(lhs, _), _), List(rhs)) if isStdCollectionMap(s.symbol) => Some((lhs,rhs))
      case Apply(TypeApply(s @ Select(lhs, _), _), List(rhs, _)) if isStdCollectionMap(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }
  
  object ExCollectionFold {
    def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
      case Apply(TypeApply(s @ Select(lhs, _), _), List(arg1,arg2)) if isStdCollectionFold(s.symbol) => Some((lhs,arg1,arg2))
      case _ => None
    }
  }

  object ExCollectionReduce {
    def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(arg1,arg2)) if isStdCollectionReduce(s.symbol) => Some((lhs,arg1,arg2))
      case _ => None
    }
  }
  
  //addition: +,++,+:,:+,::,:::

  object ExCollectionPlus {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionPlus(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionPlusColon {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionPlusColon(s.symbol) => Some((lhs,rhs))
      case Apply(TypeApply(s @ Select(lhs, _),_), List(rhs,_)) if isStdCollectionPlusColon(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionColonPlus {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionColonPlus(s.symbol) => Some((lhs,rhs))
      case Apply(TypeApply(s @ Select(lhs, _),_), List(rhs,_)) if isStdCollectionColonPlus(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }
  
  object ExCollectionCons {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionCons(s.symbol) => Some((lhs,rhs))
      case Apply(TypeApply(s @ Select(lhs, _),_), List(rhs)) if isStdCollectionCons(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }
  
  //TODO += with *
  object ExCollectionPlusEqual {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionPlusEqual(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionPlusPlus {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionPlusPlus(s.symbol) => Some((lhs,rhs))
      case Apply(TypeApply(s @ Select(lhs, _),_), List(rhs,_)) if isStdCollectionPlusPlus(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionPlusPlusEqual {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionPlusPlusEqual(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionConcat {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionConcat(s.symbol) => Some((lhs,rhs))
      case Apply(TypeApply(s @ Select(lhs, _),_), List(rhs,_)) if isStdCollectionConcat(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  //remove element: -, --, filter, filterNot
  object ExCollectionMinus {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionMinus(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionMinusMinus {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionMinusMinus(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionFilter {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionFilter(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionFilterNot {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionFilterNot(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  //choose: apply, head (this does not remove the selected element)
  
  object ExCollectionApply {
    def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
      case Apply(s @ Select(lhs, _), List(rhs)) if isStdCollectionApply(s.symbol) => Some((lhs,rhs))
      case _ => None
    }
  }

  object ExCollectionHead {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(s @ Select(lhs, _), Nil) if isStdCollectionHead(s.symbol) => Some(lhs)
      case _ => None
    }
  }

  object ExWrapper {
    def unapply(tree: Apply): Option[Tree] = tree match {
      case Apply(ScalaPredef(sym), List(arg)) if isWrapper(sym) => Some(arg)
      case Apply(TypeApply(ScalaPredef(sym),_), List(arg)) if isWrapper(sym) => Some(arg)
      case _ => None
    }
  }

}
