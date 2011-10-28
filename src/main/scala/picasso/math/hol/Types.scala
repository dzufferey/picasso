package picasso.math.hol

sealed abstract class Type {
  def freeParameters: Set[TypeVariable]
  def alpha(subst: Map[TypeVariable, Type]): Type
  
  //syntactic sugar
  def ~>(that: Type): Function = this match {
    case Function(args, ret) => Function(args ::: List(ret), that)
    case other => Function(List(this), that)
  }
}

object Type {

  var cnt = 0

  //TODO synchronise
  def freshTypeVar = {
    cnt += 1
    TypeVariable("_" + cnt)
  }

}

case object Bool extends Type {
  override def toString = "Bool"
  def freeParameters = Set[TypeVariable]()
  def alpha(subst: Map[TypeVariable, Type]) = this 
}

case object Int extends Type {
  override def toString = "Int"
  def freeParameters = Set[TypeVariable]()
  def alpha(subst: Map[TypeVariable, Type]) = this 
}

case object String extends Type {
  override def toString = "String"
  def freeParameters = Set[TypeVariable]()
  def alpha(subst: Map[TypeVariable, Type]) = this 
}

case object Wildcard extends Type {
  override def toString = "_"
  def freeParameters = Set[TypeVariable]()
  def alpha(subst: Map[TypeVariable, Type]) = this 
}

case class Product(cmpts: List[Type]) extends Type {
  override def toString = cmpts.mkString("","*","")
  def freeParameters = (Set[TypeVariable]() /: cmpts)(_ ++ _.freeParameters)
  def alpha(subst: Map[TypeVariable, Type]) = Product(cmpts.map(_.alpha(subst))) 
}

case class Function(args: List[Type], returns: Type) extends Type {
  override def toString = args.mkString("(","->","->") + returns + ")"
  def freeParameters = (returns.freeParameters /: args)(_ ++ _.freeParameters)
  def alpha(subst: Map[TypeVariable, Type]) = Function(args.map(_.alpha(subst)), returns.alpha(subst)) 
}

case class FiniteValues[T](values: List[T]) extends Type {
  override def toString = values.mkString("{",",","}")
  def freeParameters = Set[TypeVariable]()
  def alpha(subst: Map[TypeVariable, Type]) = this 
}

case class UnInterpreted(id: String) extends Type {
  override def toString = id
  def freeParameters = Set[TypeVariable]()
  def alpha(subst: Map[TypeVariable, Type]) = this 
}

case class TypeVariable(name: String) extends Type {
  override def toString = "'"+name
  def freeParameters = Set[TypeVariable](this)
  def alpha(subst: Map[TypeVariable, Type]) = subst.getOrElse(this, this)
}

case class ClassType( name: String, tparams: List[Type]) extends Type {
  override def toString = name + (if (tparams.isEmpty) "" else tparams.mkString("[",",","]"))
  def freeParameters = (Set[TypeVariable]() /: tparams.map(_.freeParameters))(_ ++ _)
  def alpha(subst: Map[TypeVariable, Type]) = ClassType(name, tparams.map(_.alpha(subst))).copyAttr(this) 
  //a series of flags that gives additional info
  var isActor = false
  var isCollection = false
  var isCase = false
  var isModule = false //unique global reference
  def copyAttr(from: ClassType): this.type = {
    isActor = from.isActor
    isCollection = from.isCollection
    isCase = from.isCase
    isModule = from.isModule
    this
  }
}

//TODO copier for Type

//TODO accessor for tuples

//TODO Unit and Nothing types ?

object Collection {
  def apply(name: String, t: Type): Type = {
    val ct = ClassType(name, t :: Nil)
    ct.isCollection = true
    ct
  }
  def unapply(tpe: Type): Option[(String, Type)] = tpe match {
    case ct @ ClassType(name, t :: Nil) if ct.isCollection => Some((name, t))
    case _ => None
  }
}

object ActorType {
  def apply(name: String, lst: List[Type]): Type = {
    val ct = ClassType(name, lst)
    ct.isActor = true
    ct
  }
  def unapply(tpe: Type): Option[(String, List[Type])] = tpe match {
    case ct @ ClassType(a, b) if ct.isActor => Some((a,b))
    case _ => None
  }
}

object CaseType {
  def apply(name: String, lst: List[Type]): Type = {
    val ct = ClassType(name, lst)
    ct.isCase = true
    ct
  }
  def unapply(tpe: Type): Option[(String, List[Type])] = tpe match {
    case ct @ ClassType(a, b) if ct.isCase => Some((a,b))
    case _ => None
  }
}

/** Channel/name in the pi-calculus sense */
object Channel {
  //not really uninterpreted, but actually pretty much interpreted
  def apply() = UnInterpreted("name")
  def unapply(tpe: Type): Boolean = tpe match {
    case UnInterpreted("name") => true
    case _ => false
  }
}
