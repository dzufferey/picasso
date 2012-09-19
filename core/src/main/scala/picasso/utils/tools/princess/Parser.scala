package picasso.utils.tools.princess

import picasso.math.hol._
import picasso.utils._
import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.combinator.syntactical._

/**Parser for princess's grammar */
object Parser extends StandardTokenParsers {
  lexical.delimiters += (";", ",", "(", ")", "{", "}", "+", "-", "->", "<->", "*", "|", "&", "!", "\\")
  lexical.reserved += ("false", "true", "int", "nat", "inf")

  def expression: Parser[Formula] = rep1sep(expression1, "<->") ^^ ( lst => sys.error("TODO")  )
  def expression1: Parser[Formula] = rep1sep(expression2, "->") ^^ ( lst => sys.error("TODO") )
  def expression2: Parser[Formula] = rep1sep(expression3, "|") ^^ ( lst => Application(Or, lst) )
  def expression3: Parser[Formula] = rep1sep(expression4, "&") ^^ ( lst => Application(And, lst) )

  def expression4: Parser[Formula] =
    ( "!" ~> expression4    ^^ ( e1 => Application(Not, List(e1)))
    | expression5
    )

  def expression5: Parser[Formula] =
    ( "true"                                ^^^ Literal(true)
    | "false"                               ^^^ Literal(false)
    | expression6 ~ relSym ~ expression6    ^^ { case e1 ~ rel ~ e2 => Application(rel, List(e1, e2)) }
    | expression6
    )

  def expression6: Parser[Formula] = sys.error("TODO")
  def expression7: Parser[Formula] = sys.error("TODO")
  def expression8: Parser[Formula] = sys.error("TODO")
  def expression9: Parser[Formula] = sys.error("TODO")

  def relSym: Parser[InterpretedFct] =
    ( ">=" ^^^ Geq
    | "<=" ^^^ Leq
    | ">"  ^^^ Gt
    | "<"  ^^^ Lt
    | "="  ^^^ Eq
    | "!=" ^^^ Neq
    )

}
