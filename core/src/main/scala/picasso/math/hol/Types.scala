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

  def freshParams(tpe: Type): (Map[TypeVariable,TypeVariable], Type) = {
    var oldParams = tpe.freeParameters
    var subst: Map[TypeVariable,TypeVariable] = (for (t <- oldParams.toSeq) yield (t, freshTypeVar)).toMap
    (subst, tpe alpha subst)
  }

  /** Are there some object which are in the intersection of the two types ?
   *  This is not exact but a good first approximation.
   *  To make thing better we should keep some information about the subtyping of ClassTypes.
   */
  def nonEmptyIntersection(tp1: Type, tp2: Type): Boolean = (tp1, tp2) match {
    case (Bool, Bool) | (Int, Int) | (String, String)
      |  (Wildcard, _) | (_, Wildcard) | (_, TypeVariable(_))
      |  (TypeVariable(_), _) => true
    case (Product(lst1), Product(lst2)) => (lst1 zip lst2) forall { case (t1, t2) => nonEmptyIntersection(t1, t2) }
    case (Function(a1, r1), Function(a2, r2)) =>
      nonEmptyIntersection(r1,r2) && 
      ((a1 zip a2) forall { case (t1, t2) => nonEmptyIntersection(t1, t2) })
    case (FiniteValues(lst1), FiniteValues(lst2)) => lst1 exists (lst2 contains _)
    case (UnInterpreted(n1), UnInterpreted(n2)) => n1 == n2
    case (c1 @ ClassType(n1, a1), c2 @ ClassType(n2, a2)) =>
      c1.isActor == c2.isActor && c1.isCollection == c2.isCollection &&
      c1.isCase == c2.isCase && c1.isModule == c2.isModule &&
      ((a1 zip a2) forall { case (t1, t2) => nonEmptyIntersection(t1, t2) })
    case (_, _) => false
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

//TODO Nothing types ?

object UnitT {
  private val instance = FiniteValues(List( () ))
  def apply(): FiniteValues[Unit] = instance
  def unapply(tpe: FiniteValues[Unit]) = tpe match {
    case FiniteValues(List( () )) => true
    case _ => false
  }
}

object Collection {
  def apply(name: String, t: Type): Type = {
    val ct = ClassType(name, t :: Nil)
    ct.isCollection = true
    ct
  }
  def unapply(tpe: ClassType): Option[(String, Type)] = tpe match {
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
  def unapply(tpe: ClassType): Option[(String, List[Type])] = tpe match {
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
  def unapply(tpe: ClassType): Option[(String, List[Type])] = tpe match {
    case ct @ ClassType(a, b) if ct.isCase => Some((a,b))
    case _ => None
  }
}

/** Channel/name in the pi-calculus sense */
object Channel {
  //not really uninterpreted, but actually pretty much interpreted
  def apply() = UnInterpreted("name")
  def unapply(tpe: UnInterpreted): Boolean = tpe match {
    case UnInterpreted("name") => true
    case _ => false
  }
}
