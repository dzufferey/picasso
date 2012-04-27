package picasso.frontend.compilerPlugin

import scala.tools.nsc.Global
import scala.reflect.NameTransformer
import scala.tools.nsc.symtab.Flags._
import picasso.graph.GT
import picasso.frontend.compilerPlugin.utils._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Level, Misc}

trait Definitions {
  self: AnalysisUniverse =>

  import global._
  import global.definitions._

  def mainMethodType(owner: Symbol): Type = {
    val strType = StringClass.typeConstructor
    val strArrayType = arrayType(strType)
    val argSym = owner.newValueParameter(NoPosition, "args") setInfo strArrayType
    MethodType(List(argSym) , UnitClass.tpe)
  }

  def isMainMethod(m: Symbol): Boolean = m.tpe <:< mainMethodType(m)

  def isMainClass(cd: Symbol) : Boolean = (
       cd.isFinal
    && cd.isModuleClass
    && cd.tpe.decl("main").isMethod
    && isMainMethod(getMember(cd, "main"))
  )

  def isString(t: Type): Boolean = t =:= StringClass.typeConstructor
  def isString(sym: Symbol): Boolean = isString(sym.info)

  def isLiteral(t: Type): Boolean = t <:< AnyValClass.typeConstructor || isString(t)
  def isLiteral(sym: Symbol): Boolean = isLiteral(sym.info)

  def isBoolean(t: Type): Boolean = t =:= BooleanClass.tpe
  def isBoolean(sym: Symbol): Boolean = isBoolean(sym.info)

  def isCaseClass(t: Type): Boolean = t.typeSymbol.isCase//t.typeSymbol.isCaseClass
  def isCaseClass(sym: Symbol): Boolean = isCaseClass(sym.info)

  def isModule(t: Type): Boolean = t.typeSymbol.isModuleClass
  def isModule(sym: Symbol): Boolean = isModule(sym.info)

  //definitions for actors
  lazy val abstractActorClass   = definitions.getClass("scala.actors.AbstractActor")
  lazy val actorClass           = definitions.getClass("scala.actors.Actor")
  lazy val reactorClass         = definitions.getClass("scala.actors.Reactor")
  lazy val replyReactorClass    = definitions.getClass("scala.actors.ReplyReactor")
  lazy val outputChannelClass   = definitions.getClass("scala.actors.OutputChannel")
  lazy val inputChannelClass    = definitions.getClass("scala.actors.InputChannel")
  lazy val actorObject          = definitions.getModule("scala.actors.Actor")
 
  lazy val bang             = newTermName( NameTransformer.encode("!"))
  lazy val bangBang         = newTermName( NameTransformer.encode("!!"))
  lazy val qmark            = newTermName( NameTransformer.encode("?"))
  lazy val bangQmark        = newTermName( NameTransformer.encode("!?"))
  
  lazy val loop             = newTermName("loop")
  lazy val loopWhile        = newTermName("loopWhile")
  
  lazy val react            = newTermName("react")
  lazy val reactWithin      = newTermName("reactWithin")
  lazy val receive          = newTermName("receive")
  lazy val receiveWithin    = newTermName("receiveWithin")
  lazy val reply            = newTermName("reply")
  lazy val send             = newTermName("send")
  lazy val sender           = newTermName("sender")
  
  lazy val act              = newTermName("act")
  lazy val start            = newTermName("start")
  lazy val restart          = newTermName("restart")
  lazy val exit             = newTermName("exit")
  
  lazy val actMethod        = getMember(actorClass, act)
  lazy val startMethod      = getMember(actorClass, start)
  lazy val restartMethod    = getMember(actorClass, restart)

  def isActorClass(t: Type): Boolean = {
    val res = (
      t <:< actorClass.tpe ||
      t.typeConstructor <:< reactorClass.typeConstructor ||
      t.typeConstructor <:< replyReactorClass.typeConstructor ||
      t.typeConstructor <:< outputChannelClass.typeConstructor ||
      t.typeConstructor <:< inputChannelClass.typeConstructor
    )
    Logger("Plugin", LogDebug, "isActorClass: " + t + " -> " + res)
    res
  }
  def isActorClass(s: Symbol): Boolean = isActorClass(s.tpe)
  
  def isActorClassOnly(t: Type): Boolean = t <:< actorClass.tpe
  def isActorClassOnly(s: Symbol): Boolean = isActorClassOnly(s.tpe)

  def isActorLoop(s: Symbol) = getMember(actorObject, loop).alternatives contains s
  def isActorLoopWhile(s: Symbol) = getMember(actorObject, loopWhile).alternatives contains s

  def isActorMethod(s: Symbol) = isActorClass(s.owner)

  def checkForActorMethod(n: Name, sym: Symbol): Boolean = {
    sym.name == n && isActorMethod(sym)
  }
  
  /** The scala tpe of sender */
  lazy val senderType = {
    val fullType = outputChannelClass.tpe
    val param = fullType.typeArgs map (_.typeSymbol)
    assert(param.size == 1)
    fullType.instantiateTypeParams(param, anyparam)
  }

  /** a dummy methods for matching ... */
  lazy val matchCase = {
    val mysym = NoSymbol.newMethod(NoPosition, nme.CASEkw)
    val tparam1 = mysym.newTypeParameter(NoPosition, newTypeName("T2"))
    val tparam2 = mysym.newTypeParameter(NoPosition, newTypeName("T2"))
    tparam1.setInfo(TypeBounds(NothingClass.typeConstructor, AnyClass.typeConstructor))
    tparam2.setInfo(TypeBounds(NothingClass.typeConstructor, AnyClass.typeConstructor))
    mysym.setInfo(PolyType(List(tparam1, tparam2), MethodType(List(tparam1, tparam2), BooleanClass.tpe)))
    mysym setFlag FINAL
  }

  //TODO might be better in TreeUtils
  object MatchCase {
    def apply(matched: Tree, pat: Tree): Tree = {
      val typed = TypeApply(Select(Ident(NoSymbol), matchCase), List(TypeTree(matched.tpe), TypeTree(pat.tpe)))
      typed setType MethodType(List(matched.tpe.typeSymbol, pat.tpe.typeSymbol), BooleanClass.tpe)
      treeCopy.Apply(pat, typed, List(matched, pat)) setType BooleanClass.tpe
    }
    def unapply(t: Tree): Option[(Tree,Tree)] = t match {
      case Apply(TypeApply(slt @ Select(_,_), _), matched :: pat :: Nil) if (slt.symbol == matchCase) => Some(matched, pat)
      case _ => None
    }
  }
  
  /** a dummy symbol for the current exception being thrown */
  lazy val errorSymbol = NoSymbol.newValue(NoPosition, nme.THROWkw) setInfo NothingClass.typeConstructor

  /** a dummy symbol for values that are discarded */
  lazy val dummySymbol = NoSymbol.newValue(NoPosition, "picasso$dummy") setInfo AnyClass.typeConstructor

  //predef object is PredefModule
  lazy val predefAssert = getMember(PredefModule, nme.assert_)
  lazy val predefAssert1 = predefAssert.alternatives.find(_.paramss(0).size == 1).get

  lazy val predefAssume = getMember(PredefModule, nme.assume_)
  lazy val predefAssume1 = predefAssume.alternatives.find(_.paramss(0).size == 1).get
  
  lazy val predefRequire = getMember(PredefModule, newTermName("require"))
  lazy val predefRequire1 = predefRequire.alternatives.find(_.paramss(0).size == 1).get

  lazy val predefAny2Ensuring = getMember(PredefModule, newTermName("any2Ensuring"))
  lazy val predefEnsuring = PredefModule.info.decls.find(s => s.name.toString == "Ensuring").get
  lazy val predefEnsuringEnsuring = getMember(predefEnsuring, newTermName("ensuring"))

  //TODO 

  def isAssert(sym: Symbol) = predefAssert.alternatives contains sym
  def isAssume(sym: Symbol) = predefAssume.alternatives contains sym

  //Boolean type
  //lazy val BooleanClass = newValueClass(nme.Boolean, BOOL_TAG, 0)
  //def Boolean_and = getMember(BooleanClass, nme.ZAND)
  //def Boolean_or  = getMember(BooleanClass, nme.ZOR)
  lazy val Boolean_not = getMember(BooleanClass, nme.UNARY_!)
  lazy val Boolean_eq  = getMember(BooleanClass, nme.EQ)
  lazy val Boolean_ne  = getMember(BooleanClass, nme.NE)
  lazy val Boolean_xor = getMember(BooleanClass, nme.XOR)

  //TODO definitions for collection/set/...
  //as part of the compiler defintitions
  //lazy val ConsClass          = getClass("scala.collection.immutable.$colon$colon")
  //lazy val IterableClass      = getClass("scala.collection.Iterable")
  //lazy val IteratorClass      = getClass("scala.collection.Iterator")
  //lazy val ListClass          = getClass("scala.collection.immutable.List")
  //lazy val SeqClass           = getClass("scala.collection.Seq")
  //lazy val StringBuilderClass = getClass("scala.collection.mutable.StringBuilder")
  //lazy val TraversableClass   = getClass("scala.collection.Traversable")
  //lazy val NilModule          = getModule("scala.collection.immutable.Nil")
  lazy val collection           = getModule("scala.collection")
  lazy val collectionPackageClass = collection.tpe.typeSymbol
  lazy val collectionMutable    = getModule("scala.collection.mutable")
  lazy val collectionImmutable  = getModule("scala.collection.immutable")

  //TODO make sure it is not a companion
  def isStdCollection(t: Type): Boolean = isStdCollection(t.typeSymbol)
  def isStdCollection(s: Symbol): Boolean = {
    val res = s.hasTransOwner(collectionPackageClass) /*TODO why package class*/ || s == ArrayClass
    res
  }
  def isStdCollectionCompanion(t: Type): Boolean = isStdCollectionCompanion(t.typeSymbol)
  def isStdCollectionCompanion(s: Symbol) = {
    val res = s.companionClass != s && (s.hasTransOwner(collectionPackageClass) /*TODO why package class*/ || s == ArrayClass.companionModule)
    res
  }

  //interesting collection classes:
  //-TraversableOnce (foreach, fold, reduce)
  //-Traversable (++, filter, head, map, drop, take, tail, filterNot)
  //-Seq (+:,:+,apply)
  lazy val traversable          = definitions.getClass("scala.collection.Traversable")
  lazy val filterMonadic        = definitions.getClass("scala.collection.generic.FilterMonadic")
    lazy val foreach1           = earliestMethod(getMember(traversable, nme.foreach))
    lazy val foreach2           = earliestMethod(getMember(filterMonadic, nme.foreach))
    lazy val map1               = earliestMethod(getMember(traversable, nme.map))
    lazy val map2               = earliestMethod(getMember(filterMonadic, nme.map))
    lazy val foldL1             = earliestMethod(getMember(traversable, newTermName(NameTransformer.encode("/:"))))
    lazy val foldR1             = earliestMethod(getMember(traversable, newTermName(NameTransformer.encode(":\\"))))
    lazy val foldL2             = earliestMethod(getMember(traversable, newTermName("foldLeft")))
    lazy val foldR2             = earliestMethod(getMember(traversable, newTermName("foldRight")))
    lazy val reduceL            = earliestMethod(getMember(traversable, newTermName("reduceLeft")))
    lazy val reduceR            = earliestMethod(getMember(traversable, newTermName("reduceRight")))
  //lazy val traversableOnce      = definitions.getClass("scala.collection.TraversableOnce")
    lazy val plusPlus           = earliestMethod(getMember(traversable, newTermName(NameTransformer.encode("++"))))
    lazy val filter             = earliestMethod(getMember(traversable, newTermName("filter")))
    lazy val filterNot          = earliestMethod(getMember(traversable, newTermName("filterNot")))
    lazy val head               = earliestMethod(getMember(traversable, nme.head))
    lazy val tail               = earliestMethod(getMember(traversable, nme.tail))
    lazy val take               = earliestMethod(getMember(traversable, newTermName("take")))
    lazy val drop               = earliestMethod(getMember(traversable, nme.drop))
    lazy val isEmpty            = earliestMethod(getMember(traversable, nme.isEmpty))
  lazy val seq                  = definitions.getClass("scala.collection.Seq")
    lazy val plusColon          = earliestMethod(getMember(seq, newTermName(NameTransformer.encode("+:"))))
    lazy val colonPlus          = earliestMethod(getMember(seq, newTermName(NameTransformer.encode(":+"))))
    lazy val apply              = earliestMethod(getMember(seq, nme.apply))
  //lazy val list                 = definitions.getClass("scala.collection.immutable.List")
    lazy val cons               = earliestMethod(getMember(ListClass, newTermName(NameTransformer.encode("::"))))
    lazy val concat             = earliestMethod(getMember(ListClass, newTermName(NameTransformer.encode(":::"))))
  //TODO addable will disappear => this is not matching anything ...
  lazy val addable              = definitions.getClass("scala.collection.generic.Addable")
    lazy val plus               = earliestMethod(getMember(addable, newTermName(NameTransformer.encode("+"))))
  lazy val subtractable         = definitions.getClass("scala.collection.generic.Subtractable")
    lazy val minus              = earliestMethod(getMember(subtractable, newTermName(NameTransformer.encode("-"))))
    lazy val minusMinus         = earliestMethod(getMember(subtractable, newTermName(NameTransformer.encode("--"))))
  lazy val growable             = definitions.getClass("scala.collection.generic.Growable")
    lazy val plusEqual          = earliestMethod(getMember(growable, newTermName(NameTransformer.encode("+="))))
    lazy val plusPlusEqual      = earliestMethod(getMember(growable, newTermName(NameTransformer.encode("++="))))
  lazy val genericCompanion     = definitions.getClass("scala.collection.generic.GenericCompanion")
    lazy val companionApply     = earliestMethod(getMember(genericCompanion, nme.apply))
    lazy val companionEmpty     = earliestMethod(getMember(genericCompanion, newTermName("empty")))
  //lazy val NilModule        = getModule("scala.collection.immutable.Nil")

  //iteration
  def isStdCollectionMap(s: Symbol) = {
    val early = earliestMethod(s)
    (map1.alternatives contains early) || (map2.alternatives contains early)
  }
  def isStdCollectionForeach(s: Symbol) = {
    val early = earliestMethod(s)
    (foreach1.alternatives contains early) || (foreach2.alternatives contains early)
  }
  def isStdCollectionFold(s: Symbol) = {
    val early = earliestMethod(s)
    val folds = List(foldL1,foldR1,foldL2,foldR2)
    folds contains early
  }
  def isStdCollectionReduce(s: Symbol) = {
    val early = earliestMethod(s)
    reduceL == early || reduceR == early
  }

  def isStdCollectionIsEmpty(s: Symbol)   = isEmpty.alternatives contains earliestMethod(s)

  //addition
  def isStdCollectionPlus(s: Symbol)      = plus.alternatives contains earliestMethod(s)
  def isStdCollectionPlusColon(s: Symbol) = plusColon.alternatives contains earliestMethod(s)
  def isStdCollectionColonPlus(s: Symbol) = colonPlus.alternatives contains earliestMethod(s)
  def isStdCollectionCons(s: Symbol)      = cons.alternatives contains earliestMethod(s)
  def isStdCollectionPlusPlus(s: Symbol)  = plusPlus.alternatives contains earliestMethod(s)
  def isStdCollectionConcat(s: Symbol)    = concat.alternatives contains earliestMethod(s)
  def isStdCollectionPlusEqual(s: Symbol) = plusEqual.alternatives contains earliestMethod(s)
  def isStdCollectionPlusPlusEqual(s: Symbol) = plusPlusEqual.alternatives contains earliestMethod(s)

  //remove
  def isStdCollectionMinus(s: Symbol)     = minus.alternatives contains earliestMethod(s)
  def isStdCollectionMinusMinus(s: Symbol)= minusMinus.alternatives contains earliestMethod(s)
  def isStdCollectionFilter(s: Symbol)    = filter.alternatives contains earliestMethod(s)
  def isStdCollectionFilterNot(s: Symbol) = filterNot.alternatives contains earliestMethod(s)

  //choose
  def isStdCollectionApply(s: Symbol)     = apply.alternatives contains earliestMethod(s)
  def isStdCollectionHead(s: Symbol)      = head.alternatives contains earliestMethod(s)

  //companion
  def isStdCollectionCompanionApply(s: Symbol) = companionApply.alternatives contains earliestMethod(s)
  def isStdCollectionCompanionEmpty(s: Symbol) = companionEmpty.alternatives contains earliestMethod(s)

  //LowPriorityImplicits (wrap)
  lazy val collectionWrap       = definitions.getClass("scala.LowPriorityImplicits")
    //lazy val wrapArray          = earliestMethod(getMember(collectionWrap, newTermName("wrapArray"))) //isOverloaded
    lazy val genericWrapArray   = earliestMethod(getMember(collectionWrap, newTermName("genericWrapArray")))
    lazy val wrapBooleanArray   = earliestMethod(getMember(collectionWrap, newTermName("wrapBooleanArray")))
    lazy val wrapByteArray      = earliestMethod(getMember(collectionWrap, newTermName("wrapByteArray")))
    lazy val wrapCharArray      = earliestMethod(getMember(collectionWrap, newTermName("wrapCharArray")))
    lazy val wrapDoubleArray    = earliestMethod(getMember(collectionWrap, newTermName("wrapDoubleArray")))
    lazy val wrapFloatArray     = earliestMethod(getMember(collectionWrap, newTermName("wrapFloatArray")))
    lazy val wrapIntArray       = earliestMethod(getMember(collectionWrap, newTermName("wrapIntArray")))
    lazy val wrapLongArray      = earliestMethod(getMember(collectionWrap, newTermName("wrapLongArray")))
    lazy val wrapRefArray       = earliestMethod(getMember(collectionWrap, newTermName("wrapRefArray")))
    lazy val wrapShortArray     = earliestMethod(getMember(collectionWrap, newTermName("wrapShortArray")))
    lazy val wrapUnitArray      = earliestMethod(getMember(collectionWrap, newTermName("wrapUnitArray")))
    lazy val wrapString         = earliestMethod(getMember(collectionWrap, newTermName("wrapString")))
    lazy val booleanArrayOps    = earliestMethod(getMember(PredefModule, newTermName("booleanArrayOps")))
    lazy val byteArrayOps       = earliestMethod(getMember(PredefModule, newTermName("byteArrayOps")))
    lazy val charArrayOps       = earliestMethod(getMember(PredefModule, newTermName("charArrayOps")))
    lazy val doubleArrayOps     = earliestMethod(getMember(PredefModule, newTermName("doubleArrayOps")))
    lazy val floatArrayOps      = earliestMethod(getMember(PredefModule, newTermName("floatArrayOps")))
    lazy val genericArrayOps    = earliestMethod(getMember(PredefModule, newTermName("genericArrayOps")))
    lazy val intArrayOps        = earliestMethod(getMember(PredefModule, newTermName("intArrayOps")))
    lazy val longArrayOps       = earliestMethod(getMember(PredefModule, newTermName("longArrayOps")))
    lazy val refArrayOps        = earliestMethod(getMember(PredefModule, newTermName("refArrayOps")))
    lazy val shortArrayOps      = earliestMethod(getMember(PredefModule, newTermName("shortArrayOps")))
    lazy val unitArrayOps       = earliestMethod(getMember(PredefModule, newTermName("unitArrayOps")))


  lazy val allWrapper = List(
    /*wrapArray,*/ genericWrapArray, booleanArrayOps, byteArrayOps,
    charArrayOps, doubleArrayOps, floatArrayOps, genericArrayOps,
    intArrayOps, longArrayOps, refArrayOps, shortArrayOps,
    unitArrayOps, wrapBooleanArray, wrapByteArray, wrapCharArray,
    wrapDoubleArray, wrapFloatArray, wrapIntArray, wrapLongArray,
    wrapRefArray, wrapShortArray, wrapUnitArray, wrapString
  )
  lazy val allWrapperSymbols = allWrapper flatMap (_.alternatives)
  def isWrapper(s: Symbol) = allWrapperSymbols contains earliestMethod(s)

}
