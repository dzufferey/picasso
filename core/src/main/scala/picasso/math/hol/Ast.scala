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

  def alpha(map: Map[Variable, Variable]): Formula

  val freeVariables: Set[Variable]
  val boundVariables: Set[Variable]
}

object Formula {

  protected def flatten1(i: InterpretedFct, f: Formula): List[Formula] = f match {
    case Application(`i`, lst) => lst.flatMap(flatten1(i, _))
    case Application(other, lst) => List(Application(other, lst map flatten))
    case Binding(b, v, f) => List(Binding(b, v, flatten(f)))
    case other => List(other)
  }

  def flatten(f: Formula): Formula = f match {
    case Application(Plus, lst) => Application(Plus, lst.flatMap(flatten1(Plus, _)))
    case Application(And, lst) => Application(And, lst.flatMap(flatten1(And, _)))
    case Application(Or, lst) => Application(Or, lst.flatMap(flatten1(Or, _)))
    case Application(other, lst) => Application(other, lst map flatten)
    case Binding(b, v, f) => Binding(b, v, flatten(f))
    case other => other
  }
}

case class Literal[T](value: T) extends Formula {

  override def toString = value.toString

  def alpha(map: Map[Variable, Variable]) = this
  lazy val freeVariables: Set[Variable] = Set[Variable]()
  lazy val boundVariables: Set[Variable] = Set[Variable]()

}

//Actually more like a Constant, not a Variable
case class Variable(name: String) extends Formula {

  override def toString = name

  def alpha(map: Map[Variable, Variable]) = map.getOrElse(this, this)
  lazy val freeVariables: Set[Variable] = Set[Variable](this)
  lazy val boundVariables: Set[Variable] = Set[Variable]()

}

case class Application(fct: Formula, args: List[Formula]) extends Formula {

  override def toString = fct.toString + args.mkString("(",", ",")")

  def alpha(map: Map[Variable, Variable]) = Application(fct, args.map(_.alpha(map)))
  lazy val freeVariables: Set[Variable] = (Set[Variable]() /: args)(_ ++ _.freeVariables)
  lazy val boundVariables: Set[Variable] = (Set[Variable]() /: args)(_ ++ _.boundVariables)

}

sealed abstract class InterpretedFct(symbol: String) extends Formula {
  def alpha(map: Map[Variable, Variable]) = this
  val freeVariables: Set[Variable] = Set[Variable]()
  val boundVariables: Set[Variable] = Set[Variable]()
  override def setType(t: Type): this.type = {
    assert(t == tpe, "type of " + symbol + " (InterpretedFct) cannot be changed")
    this
  }
}

case object Not extends InterpretedFct("~") {
  tpe = Bool ~> Bool
}

case object And extends InterpretedFct("&") {
  tpe = Bool ~> Bool ~> Bool
}
case object Or extends InterpretedFct("|") {
  tpe = Bool ~> Bool ~> Bool
}
case object Implies extends InterpretedFct("->") {
  tpe = Bool ~> Bool ~> Bool
}

case object Eq extends InterpretedFct("=") {
  tpe = Int ~> Int ~> Bool
  //tpe = TypeVariable("A") ~> TypeVariable("A") ~> Bool
}
case object Neq extends InterpretedFct("~=") {
  tpe = Int ~> Int ~> Bool
  //tpe = TypeVariable("A") ~> TypeVariable("A") ~> Bool
}

case object Plus extends InterpretedFct("+") {
  tpe = Int ~> Int ~> Int
}
case object Minus extends InterpretedFct("-") {
  tpe = Int ~> Int ~> Int
}
case object Times extends InterpretedFct("*") {
  tpe = Int ~> Int ~> Int
}
case object Divides extends InterpretedFct("/") {
  tpe = Int ~> Int ~> Int
}

case object Leq extends InterpretedFct("<=") {
  tpe = Int ~> Int ~> Bool
}
case object Geq extends InterpretedFct(">=") {
  tpe = Int ~> Int ~> Bool
}
case object Lt extends InterpretedFct("<") {
  tpe = Int ~> Int ~> Bool
}
case object Gt extends InterpretedFct(">") {
  tpe = Int ~> Int ~> Bool
}


sealed abstract class BindingType

case class Binding(binding: BindingType, vs: List[Variable], f: Formula) extends Formula {

  override def toString = binding + " " + vs.mkString(""," ","") + ". " + f

  def alpha(map: Map[Variable, Variable]) = Binding(binding, vs, f.alpha(map -- vs))
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
