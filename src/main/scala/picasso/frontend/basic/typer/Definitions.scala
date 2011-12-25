package picasso.frontend.basic.typer

import picasso.math.hol.{Bool => BoolT, Application => _, _}
import picasso.frontend.basic._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

class Definition(val name: String, val tpe: Type, val typeParams: List[TypeVariable] = Nil) {
  val symbol = Symbol(name)

  override def toString = name + "#" + symbol.id + ": " + (if (typeParams != Nil) typeParams.mkString("[",",","]") else "") + tpe

  def arity = tpe match {
    case Function(lst, _) => lst.size 
    case ClassType(_, lst) => lst.size 
    case _ => 0
  }

  def argsType = tpe match {
    case Function(lst, _) => lst
    case ClassType(_, lst) => lst
    case other => Nil
  }
  
  def returnType = tpe match {
    case Function(_, ret) => ret
    case other => other
  }

  def freshCopyOfType: (List[TypeVariable], Type) = {
    val fresh = typeParams.map( _ => Type.freshTypeVar)
    val subst = (typeParams zip fresh).toMap
    val freshT = tpe.alpha(subst)
    (fresh, freshT)
  }

  def apply(args: Expression*): Application = {
    val argsLst = args.toList
    val actualArgsTypes = argsLst.map(_.tpe)
    assert((Set[TypeVariable]() /: actualArgsTypes)(_ ++ _.freeParameters).intersect(typeParams.toSet).isEmpty)
    Typer.unify(Function(actualArgsTypes, returnType), tpe) match {
      case Some(map) => Application(name, argsLst) setSymbol symbol setType returnType.alpha(map)
      case None => Logger.logAndThrow("Definitions", LogError, "Cannot instanciate " + this + " with " + args.mkString("(",", ",")"))
    }
  }

}

object Definitions {

  val definitions = scala.collection.mutable.HashSet[Definition]()

  val symbolIndex = scala.collection.mutable.HashMap[Symbol, Definition]()

  val nameIndex = scala.collection.mutable.HashMap[String, List[Definition]]()

  def forName(name: String) = nameIndex.getOrElse(name, Nil)

  def register(deff: Definition) {
    definitions += deff
    symbolIndex += (deff.symbol -> deff)
    nameIndex += (deff.name -> (deff :: nameIndex.getOrElse(deff.name, Nil)))
  }

  def newDefinition(name: String, tpe: Type, typeParams: List[TypeVariable]): Definition = {
    val deff = new Definition(name, tpe, typeParams)
    register(deff)
    deff
  }
  def newDefinition(name: String, tpe: Type): Definition = newDefinition(name, tpe, tpe.freeParameters.toList)

  def printAllDefinitions = for(d <- definitions) Console.println(d)

  val a = TypeVariable("A") //a sample type param
  val collT = ClassType("Bag", List(a))
  def freshCollT = {
    val fresh = Type.freshTypeVar
    (fresh, collT.alpha(Map( a -> fresh )))
  }

  //channel
  val newChannel = newDefinition("newChannel", Function(Nil, Channel()))
  val assertDef = newDefinition("assert", BoolT ~> UnitT())
  val assumeDef = newDefinition("assume", BoolT ~> UnitT())

  //boolean
  val and = newDefinition("&&", BoolT ~> BoolT ~> BoolT)
  val or = newDefinition("||", BoolT ~> BoolT ~> BoolT)
  val xor = newDefinition("^", BoolT ~> BoolT ~> BoolT)
  val not = newDefinition("!", BoolT ~> BoolT)
  val equ = newDefinition("=", a ~> a ~> BoolT)
  val neq = newDefinition("!=", a ~> a ~> BoolT)
  val random = newDefinition("random", Function(Nil, BoolT))

  //collection
  val CollectionNew     = newDefinition("newBag", Function(Nil, collT))
  val CollectionIsEmpty = newDefinition("isEmpty", collT ~> BoolT)
  val CollectionAdd     = newDefinition("add",  collT ~> a ~> UnitT() )
  val CollectionMinus   = newDefinition("remove", collT ~> a ~> UnitT() )
  val CollectionChoose  = newDefinition("choose", collT ~> a)
  val CollectionPick    = newDefinition("pick", collT ~> a)

}
