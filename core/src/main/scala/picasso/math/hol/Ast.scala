package picasso.math.hol


//TODO what about some way to do something with the formula (+, -, *, &&, ||, ^, ...)
//TODO substitution of variables
//TODO look at the gist.logic for some example (also type checking)

sealed abstract class Formula {

  def toStringFull = "(" + toString + ": " + tpe + ")"

  var tpe: Type = Wildcard
  //TODO type checking

  def setType(t: Type): this.type = {
    tpe = t
    this
  }

  val freeVariables: Set[Variable]
  val boundVariables: Set[Variable]
}

case class Literal[T](value: T) extends Formula {

  override def toString = value.toString

  lazy val freeVariables: Set[Variable] = Set[Variable]()
  lazy val boundVariables: Set[Variable] = Set[Variable]()

}

case class Variable(name: String) extends Formula {

  override def toString = name

  lazy val freeVariables: Set[Variable] = Set[Variable](this)
  lazy val boundVariables: Set[Variable] = Set[Variable]()

}

case class Application(fct: Formula, args: List[Formula]) extends Formula {

  override def toString = fct.toString + args.mkString("(",", ",")")

  lazy val freeVariables: Set[Variable] = Set[Variable]()
  lazy val boundVariables: Set[Variable] = Set[Variable]()

}

sealed abstract class BindingType

case class Binding(binding: BindingType, vs: List[Variable], f: Formula) extends Formula {

  override def toString = binding + " " + vs.mkString(""," ","") + ". " + f

  lazy val freeVariables: Set[Variable] = f.freeVariables -- vs
  lazy val boundVariables: Set[Variable] = f.boundVariables ++ vs

}

case object ForAll extends BindingType {
  def unapply(f: Formula): Option[(List[Variable],Formula)] = f match {
    case Binding(ForAll, v, f) => Some(v,f)
    case _ => None
  }
  def apply(vs:List[Variable], f: Formula) = {
    val fa = Binding(ForAll, vs, f)
    fa.tpe = Bool
    fa
  }
}
case object Exists extends BindingType {
  def unapply(f: Formula): Option[(List[Variable],Formula)] = f match {
    case Binding(Exists, v, f) => Some(v,f)
    case _ => None
  }
  def apply(vs:List[Variable], f: Formula) = {
    val ex = Binding(Exists, vs, f)
    ex.tpe = Bool
    ex
  }
}
case object Lambda extends BindingType {
  def unapply(f: Formula): Option[(List[Variable],Formula)] = f match {
    case Binding(Lambda, v, f) => Some(v,f)
    case _ => None
  }
  def apply(vs:List[Variable], f: Formula) = {
    val la = Binding(Lambda, vs, f)
    la.tpe = Function(vs map (_.tpe), f.tpe)
    la
  }
}

/** Encode "let var = expr in body" using "(λ var. body) expr" */
object Let {
  def unapply(f: Formula): Option[(List[(Variable, Formula)], Formula)] = f match {
    case Application(Lambda(vars, body), defs) if vars.length == defs.length => Some(vars zip defs, body)
    case _ => None
  }

  def apply(defs: List[(Variable, Formula)], body: Formula): Formula = {
    val (vars, forms) = defs.unzip
    val lambda = Lambda(vars, body)
    lambda.tpe = Function(forms map (_.tpe), body.tpe)
    val let = Application(lambda, forms)
    let.tpe = body.tpe
    let
  }
}