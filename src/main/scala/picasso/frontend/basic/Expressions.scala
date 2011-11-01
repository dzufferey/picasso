package picasso.frontend.basic

import picasso.math.hol.{Type, Wildcard => WildcardT}

sealed abstract class Expression extends scala.util.parsing.input.Positional with Typed

abstract class SymExpr extends Expression with Sym

case class Value(l: Literal) extends Expression {
  setType(l.tpe)
  override def toString = l.toString
}
case class ID(id: String) extends SymExpr {
  override def toString = id 
  def toStringFull = {
    if (tpe == WildcardT) toString
    else id+":"+tpe
  }
}
case class Application(fct: String, args: List[Expression]) extends SymExpr {
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
  def unapply(e: Expression): Boolean = e match {
    case Application("new-set", Nil) => true
    case _ => false
  }
}

object NewChannel {
  def apply() = Application("newChannel", Nil)
  def unapply(e: Expression): Boolean = e match {
    case Application("newChannel", Nil) => true
    case _ => false
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
  def id2ID(id: ID): picasso.ast.ID = picasso.ast.ID(picasso.math.hol.Variable(id.id) setType id.tpe) //default mode is LocalScope
  def value2Value(v: Value): picasso.ast.Expression = v.l match {
    case b @ Bool(_) => picasso.ast.Value[Boolean](Literals.bool2Lit(b))
    case s @ StringVal(_) => picasso.ast.Value[String](Literals.string2Lit(s))
  }
  def app2App(a: Application): picasso.ast.Application = a match {
    case Create(c, args) => picasso.ast.Create(c, args map exp2Exp)
    case NewChannel() => picasso.ast.NewChannel()
    case EmptySet() => picasso.ast.EmptySet()
    case _ => picasso.ast.Application(a.fct, a.args map exp2Exp)
  }
  def tuple2Tuple(t: Tuple): picasso.ast.Tuple = picasso.ast.Tuple(t.values map exp2Exp)
  implicit def exp2Exp(e: Expression): picasso.ast.Expression = e match {
    case Any => any2Any
    case id @ ID(_) => id2ID(id)
    case v @ Value(_) => value2Value(v)
    case a @ Application(_,_) => app2App(a)
    case t @ Tuple(_) => tuple2Tuple(t)
  }

}
