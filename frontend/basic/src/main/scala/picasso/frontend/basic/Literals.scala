package picasso.frontend.basic

import picasso.math.hol.{Literal => HLiteral, Bool => HBool, String => HString}

sealed abstract class Literal extends scala.util.parsing.input.Positional with Typed

case class Bool(b: Boolean) extends Literal {
  this.setType(HBool)
  override def toString = b.toString
}

//case class Integer(i: Int)  extends Literal

case class StringVal(str: String) extends Literal {
  this.setType(HString)
  override def toString = ("\""+str+"\"")
}

object Literals {
  def apply(b: Boolean) = Bool(b)
  def apply(s: String) = StringVal(s)

  def bool2Lit(l: Bool): HLiteral[Boolean] = picasso.ast.Bool(l.b)
  def string2Lit(l: StringVal): HLiteral[String] = picasso.ast.StringVal(l.str)
}
