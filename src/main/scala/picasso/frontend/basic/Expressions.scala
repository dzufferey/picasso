package picasso.frontend.basic

sealed abstract class Expression extends scala.util.parsing.input.Positional
case class Value(l: Literal) extends Expression {
  override def toString = l.toString
}
case class ID(smth: String) extends Expression {
  override def toString = smth
}
case class Application(fct: String, args: List[Expression]) extends Expression {
  override def toString = fct + args.mkString("(", ", " ,")")
}
case class Tuple(values: List[Expression]) extends Expression {
  override def toString = values.mkString("(", ", " ,")")
}
case object Any extends Expression

////////////////
// Extractors //
////////////////

object Unit {
  def apply() = Tuple(Nil)
  def unapply(e: Expression): Option[Unit] = e match {
    case Tuple(Nil) => Some(())
    case _ => None
  }
}

object EmptySet {
  def apply() = Application("new-set", Nil)
  def unapply(e: Expression): Option[Unit] = e match {
    case Application("new-set", Nil) => Some()
    case _ => None
  }
}

object NewChannel {
  def apply() = Application("new-channel", Nil)
  def unapply(e: Expression): Option[Unit] = e match {
    case Application("new-channel", Nil) => Some()
    case _ => None
  }
}

object Create {
  def apply(name: String, args: List[Expression]) = Application("create", ID(name) :: args)
  def unapply(e: Expression): Option[(String, List[Expression])] = e match {
    case Application("create", ID(name) :: args) => Some(name, args)
    case _ => None
  }
}

//TODO more extractors

////////////////////////////
// object for conversions //
////////////////////////////

object Expressions {

  def any2Any = picasso.ast.Any
  def id2ID(id: ID): picasso.ast.ID = picasso.ast.ID(picasso.math.hol.Variable(id.smth)) //default mode is LocalScope
  def value2Value(v: Value): picasso.ast.Expression = v.l match {
    case b @ Bool(_) => picasso.ast.Value[Boolean](Literals.bool2Lit(b))
    case s @ StringVal(_) => picasso.ast.Value[String](Literals.string2Lit(s))
  }
  def app2App(a: Application): picasso.ast.Application = picasso.ast.Application(a.fct, a.args map exp2Exp)
  def tuple2Tuple(t: Tuple): picasso.ast.Tuple = picasso.ast.Tuple(t.values map exp2Exp)
  implicit def exp2Exp(e: Expression): picasso.ast.Expression = e match {
    case Any => any2Any
    case id @ ID(_) => id2ID(id)
    case v @ Value(_) => value2Value(v)
    case a @ Application(_,_) => app2App(a)
    case t @ Tuple(_) => tuple2Tuple(t)
  }

}
