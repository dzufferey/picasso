package picasso.frontend.compilerPlugin.utils

import scala.tools.nsc.Global
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

//TODO is there a way to also have this in PiccoloPlugin ??
trait TreeUtils {

  val global: Global

  import global._
  import global.definitions._


  /** Most general transformer */
  class MGT(transformation: PartialFunction[Tree,Tree]) extends Transformer {
    override def transform(tree: Tree): Tree = {
      transformation.lift(tree) getOrElse super.transform(tree)
    }
  }
  
  def mgt(transformation: PartialFunction[Tree,Tree], what: Tree): Tree = {
    val mapper = new MGT(transformation)
    mapper.transform(what)
  }

  class TreeRefSubstituter(from: List[Symbol], to: List[Tree]) extends Transformer {
    override def transform(tree: Tree): Tree = tree match {
      case ref: RefTree =>
        //Logger("Plugin", LogDebug, "substituteRef: " + ref + " with " + ref.symbol)
        def subst(from: List[Symbol], to: List[Tree]): Option[Tree] =
          if (from.isEmpty) None
          else if (tree.symbol == from.head) Some(to.head)
          else subst(from.tail, to.tail);
        subst(from, to) getOrElse (super.transform(ref))
      case _ =>
        super.transform(tree)
    }
  }
    
  def substituteRef(from: List[Symbol], to: List[Tree], what: Tree): Tree = {
    Logger("Plugin", LogDebug, "substituteRef: " + (from zip to).map(p => p._1 + "->" + p._2).mkString("",", ",""))
    val substituer = new TreeRefSubstituter(from, to)
    substituer.transform(what)
  }


  class AnyTreeSubstituer(from: List[Tree], to: List[Tree]) extends Transformer {
    override def transform(tree: Tree): Tree = {
      if (from contains tree) {
        def subst(from: List[Tree], to: List[Tree]): Tree =
          if (from.isEmpty) tree
          else if (tree == from.head) to.head
          else subst(from.tail, to.tail);
        subst(from, to)
      } else {
        super.transform(tree)
      }
    }
  }

  def substituteTree(from: List[Tree], to: List[Tree], what: Tree): Tree = {
    val substituer = new AnyTreeSubstituer(from, to)
    substituer.transform(what)
  }

  def treeContains(tree: Tree, p: Tree => Boolean): Boolean = {
    val finder = new FindTreeTraverser(p)
    finder.traverse(tree)
    finder.result.isDefined
  }

  def findInTree(tree: Tree, p: Tree => Boolean): List[Tree] = {
    val finder = new FilterTreeTraverser(p)
    finder.traverse(tree)
    finder.hits.toList
  }


  /** return the position of the last statment */
  def lastStmt(body: Tree): Position = body match {
    case PackageDef(_, stats) => stats.lastOption map (lastStmt(_)) getOrElse body.pos
    case ClassDef(_, _, _, impl) => lastStmt(impl)
    case ValDef(_, _, _, rhs) => lastStmt(rhs)
    case DefDef(_, _, _, _, _, rhs) => lastStmt(rhs)
    case TypeDef(_, _, _, rhs) => lastStmt(rhs)
    case LabelDef(_, _, rhs) => lastStmt(rhs)
    case Template(_, _, stats) => stats.lastOption map (lastStmt(_)) getOrElse body.pos
    case Block(_, expr) => lastStmt(expr)
    case CaseDef(_, _, body) => lastStmt(body)
    case If(_, thenp, EmptyTree) => lastStmt(thenp)
    case If(_, _, elsep) => lastStmt(elsep)
    case Match(_, cases) => cases.lastOption map (lastStmt(_)) getOrElse body.pos
    case Try(stmts, Nil, EmptyTree) => lastStmt(stmts)
    case Try(_, catches, EmptyTree) => catches.lastOption map (lastStmt(_)) getOrElse body.pos
    case Try(_, _, finalizer) => lastStmt(finalizer)
    case tree => tree.pos
  }
    
  def decomposeBlock(tree: Tree): (List[Tree],Tree) = tree match {
    case Block(lst, expr) => (lst, expr)
    case other => (Nil, other)
  }

  def makeBlock(copied: Tree, lst: List[Tree], expr: Tree): Tree = lst match {
    case Nil => expr
    case x :: _ => expr match {
      case EmptyTree => makeBlock(copied, lst.init, lst.last)
      case _ =>
        val (blk, lastExpr) = decomposeBlock(expr)
        treeCopy.Block(copied, lst:::blk, lastExpr) setType lastExpr.tpe
    }
  }

  def makeAnonFun(args: List[Symbol], body: Tree) = {
    val argsTree = args map ( a => ValDef(a) )
    Function(argsTree, body) setPos body.pos setType MethodType(args, body.tpe)
  }

  def symbolsOwnedBy(tree: Tree, owner: Symbol): List[Tree] =
    findInTree(tree, (p => p.hasSymbol && p.symbol.hasTransOwner(owner)))

  def symbolsOwnedByDirect(tree: Tree, owner: Symbol): List[Tree] =
    findInTree(tree, (p => p.hasSymbol && p.symbol != NoSymbol && p.symbol.owner == owner))

  def changeSymbolOwner(oldOwner: Symbol, newOwner: Symbol, where: Symbol) = {
    def find(s: Symbol): Symbol = if (s.owner != oldOwner) s.cloneSymbol(find(s.owner)) else s.cloneSymbol(newOwner)
    if (where.hasTransOwner(oldOwner)) find(where)
    else where
  }

  //Do not change owners
  def substSymbol(from: List[Symbol], to: List[Symbol], what: Tree): Tree = {
    val substituer = new TreeSymSubstituter(from, to)
    substituer.transform(what)
  }
  //works on DefDef or ValDef
  def substSymbolFull(from: Symbol, to: Symbol, what: Tree): Tree = {
    val substituer = new TreeSymSubstituter(List(from), List(to))
    val result = substituer.transform(what)
    result setSymbol changeSymbolOwner(from, to, result.symbol)
  }

  def symbolsIn(tree: Tree): Set[Symbol] = {
    val init = if (tree.hasSymbol) Set[Symbol](tree.symbol) else Set[Symbol]()
    (init /: tree.children)(_ ++ symbolsIn(_))
  }

  /** make only sense when applied to methods */
  class ValDefExtractor(clazz: Option[Symbol]) extends Transformer {
    val hits = new scala.collection.mutable.ListBuffer[ValDef]
    override def transform(tree: Tree): Tree = tree match {
      case vd @ ValDef(mods, name, tpt, rhs) =>
        hits += treeCopy.ValDef(vd, mods, name, tpt, EmptyTree)// setSymbol vd.symbol setType vd.tpe
        val select = clazz map (cl => Select(This(cl) setType cl.info, vd.symbol) setType vd.symbol.info)
        val lhs = select getOrElse (Ident(vd.symbol) setType vd.symbol.info)
        Assign(lhs, transform(rhs))
      case dd @ DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        //fetch the vparamss but do not remove them
        for (lst <- vparamss; vd <- lst) hits += vd
        treeCopy.DefDef(dd, mods, name, tparams, vparamss, tpt, transform(rhs))
      case _ => super.transform(tree)
    }
  }
  
  def extractValDefs(what: Tree, clazz: Symbol = NoSymbol): (Tree, List[ValDef]) = {
    val extractor = new ValDefExtractor(if (clazz == NoSymbol) None else Some(clazz))
    val result = extractor.transform(what)
    (result, extractor.hits.toList)
  }

  def extractValDefDefs(what: DefDef, clazz: Symbol = NoSymbol): (DefDef, List[ValDef]) = {
    val (tree, hits) = extractValDefs(what, clazz)
    val result = tree.asInstanceOf[DefDef]
    (result, hits)
  }

  class NewAsSelect(of: List[Symbol]) extends Transformer {
    override def transform(tree: Tree) = tree match {
      case slt @ Select(New(tpt), n)
        if ((of contains tpt.tpe.typeSymbol) && (n == nme.CONSTRUCTOR)) =>
          Select(This(tpt.tpe.typeSymbol), slt.symbol)
      case _ => super.transform(tree)
    }
  }

  def newAsSelect(of: List[Symbol], what: Tree): Tree = {
    val transformer = new NewAsSelect(of)
    transformer.transform(what)
  }

  def getSymbolDeep(t: Tree): Symbol = t match {
    case Typed(e,_) => getSymbolDeep(e)
    case _ => t.symbol
  }

  def headString(tree: Tree): String = tree match {
    case p: Product => p.productPrefix
    case tree => "unknown: " + tree
  }

  def getterOf(clazz: ClassDef, value: Symbol): Symbol = value.getter(clazz.symbol)

  def setterOf(clazz: ClassDef, value: Symbol): Symbol = value.setter(clazz.symbol)

  def valueOfGetterSetter(clazz: Symbol, gsetter: Symbol): Symbol = {
    val name = gsetter.name
    val getterName = if (gsetter.isSetter) nme.setterToGetter(name) else nme.getterName(name)
    val valName = nme.getterToLocal(getterName)
    clazz.info.decl(valName) filter (_.isValue)
  }

  /** Use this to look for value inside the classdef, rather than the symbol */
  def valueOfGetterSetterStructural(clazz: ClassDef, gsetter: Symbol) = {
    val name = gsetter.name
    val getterName = if (gsetter.isSetter) nme.setterToGetter(name) else nme.getterName(name)
    val valName = nme.getterToLocal(getterName)
    def findValue(t: Tree): Boolean = t match {
      case ValDef(mods, name, tpt, rhs) => valName == name
      case _ => false
    }
    val candidates = clazz.impl.body filter findValue
    assert(candidates.size <= 1)
    candidates.headOption.map(_.symbol).getOrElse(NoSymbol)
  }

  private lazy val duplicator = new Transformer {
    override val treeCopy = new StrictTreeCopier
    override def transform(t: Tree) = {
      val t1 = super.transform(t)
      if ((t1 ne t) && t1.pos.isRange) t1 setPos t.pos.focus
      t1
    }
  }
  def duplicateTree(tree: Tree): Tree = duplicator transform tree

  class FindSuperCalls extends Traverser {

    import scala.collection.mutable.ListBuffer
    val hits: ListBuffer[Tree] = new ListBuffer[Tree]

    //assume unfolded expressions
    def containsSuper(tree: Tree): Boolean = tree match {
      case Super(_, _) => true
      case Select(prefix, _) => containsSuper(prefix)
      case _ => false
    }

    override def traverse(tree: Tree): Unit = tree match {
      case Super(_, _) => hits += tree
      case Select(prefix, _) => if (containsSuper(prefix)) hits += tree
      case _ => super.traverse(tree)
    }

  }
  def findSuperCalls(tree: Tree): List[Tree] = {
    val finder = new FindSuperCalls
    finder traverse tree
    finder.hits.toList
  }
  
  class FindSuperAccessorCalls extends Traverser {

    import scala.collection.mutable.ListBuffer
    val hits: ListBuffer[Tree] = new ListBuffer[Tree]

    override def traverse(tree: Tree): Unit = tree match {
      case slt @ Select(prefix, _) =>
        super.traverse(prefix)
        if (slt.symbol.isSuperAccessor) hits += tree
      case _ => super.traverse(tree)
    }

  }
  def findSuperAccessorCalls(tree: Tree): List[Tree] = {
    val finder = new FindSuperAccessorCalls
    finder traverse tree
    finder.hits.toList
  }

  def findSuperAndAccessorCalls(tree: Tree) =
    findSuperCalls(tree) ++ findSuperAccessorCalls(tree)

  def getValueOrAccesorsSymbol(tree: Tree): List[Symbol] = {
    val childrenSym = tree.children flatMap getValueOrAccesorsSymbol
    if (tree.hasSymbol && (tree.symbol.isGetter || tree.symbol.isSuperAccessor || tree.symbol.isValue || tree.symbol.isVariable)) {
      tree.symbol :: childrenSym
    } else {
      childrenSym
    }
  }

  /** Returns a list dependencies extracted from the tree.
   *  A dependency is a pair symbol depends on symbol list.
   */
  def symbolsInvloved(tree: Tree): List[(Symbol, List[Symbol])] = tree match {
    case vd @ ValDef(mods, name, tpt, rhs) =>// mods val name: tpt = rhs
      val recurse = symbolsInvloved(rhs)
      val lhsSym = vd.symbol 
      val rhsSym = getValueOrAccesorsSymbol(rhs)
      (lhsSym -> rhsSym) :: recurse
    case as @ Assign(lhs, rhs) =>// lhs = rhs
      val recurse = symbolsInvloved(rhs)
      if (lhs.symbol != NoSymbol) {
        val lhsSym = as.symbol 
        val rhsSym = getValueOrAccesorsSymbol(rhs)
        (lhsSym -> rhsSym) :: recurse
      } else {
        recurse
      }
    case Apply(fun, args) =>
      val recurse = (fun::args) flatMap symbolsInvloved
      //the interesting cases (assuming no side effect inside other methods)
      if (fun.symbol.isSetter) {
        val lhsSym = fun.symbol 
        val rhsSym = args flatMap getValueOrAccesorsSymbol
        (lhsSym -> rhsSym) :: recurse
      } else {
        recurse
      }

    case ClassDef(mods, name, tparams, impl) => symbolsInvloved(impl)
    case PackageDef(pid, stats) => stats flatMap symbolsInvloved
    case DefDef(mods, name, tparams, vparamss, tpt, rhs) => symbolsInvloved(rhs)
    case LabelDef(name, params, rhs) => symbolsInvloved(rhs)
    case Template(parents, self, body) => body flatMap symbolsInvloved
    case Block(stats, expr) => (stats ::: List(expr)) flatMap symbolsInvloved
    case CaseDef(pat, guard, body) => symbolsInvloved(body)
    case If(cond, thenp, elsep) => (cond::thenp::elsep::Nil) flatMap symbolsInvloved
    case Match(selector, cases) => (selector::cases) flatMap symbolsInvloved
    case Return(expr) => symbolsInvloved(expr)
    case Try(block, catches, finalizer) => (block::catches:::List(finalizer)) flatMap symbolsInvloved
    case Throw(expr) => symbolsInvloved(expr)
    case Typed(expr, tpt) => symbolsInvloved(expr)
    case TypeApply(fun, args) => symbolsInvloved(fun)
    case Select(qualifier, selector) => symbolsInvloved(qualifier)
    case EmptyTree | TypeDef(_,_,_,_) | ArrayValue(_,_) => Nil
    case New(_) | Super(_,_) |  This(_) | Ident(_) | Literal(_) => Nil
    case _ => Logger.logAndThrow("Plugin", LogError, "Constructor.symbolsInvloved: not expected " + tree)
  }

}
