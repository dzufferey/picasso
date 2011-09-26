package picasso.math.hol

sealed abstract class Type
case object Bool extends Type { override def toString = "Bool" }
case object Int extends Type { override def toString = "Int" }
case object String extends Type { override def toString = "String" }
case object Wildcard extends Type { override def toString = "_" }
case class Function(args: List[Type], returns: Type) extends Type {
 override def toString = args.mkString("(","->","->") + returns + ")"
}
case class FiniteValues[T](values: List[T]) extends Type
case class UnInterpreted(id: String) extends Type
case class ClassType( name: String, tparams: List[Type]) extends Type {
  override def toString = name + (if (tparams.isEmpty) "" else tparams.mkString("[",",","]"))
  //a series of flags that gives additional info
  var isActor = false
  var isCollection = false
  var isCase = false
  var isModule = false //unique global reference
}

//TODO copier for Type

//TODO accessor for tuples

//TODO Unit and Nothing types ?

object Collection {
  def unapply(tpe: Type): Option[(String, Type)] = tpe match {
    case ct @ ClassType(name, t :: Nil) if ct.isCollection => Some((name, t))
    case _ => None
  }
}

object ActorType {
  def unapply(tpe: Type): Option[(String, List[Type])] = tpe match {
    case ct @ ClassType(a, b) if ct.isActor => Some((a,b))
    case _ => None
  }
}

/** Channel/name in the pi-calculus sense */
object Channel {
  def apply() = FiniteValues[String](List("name"))
  def unapply(tpe: Type): Boolean = tpe match {
    case FiniteValues(List("name")) => true
    case _ => false
  }
}
