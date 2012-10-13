package picasso.utils.tools.princess

import picasso.math.hol._
import picasso.utils._
import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.combinator.syntactical._

/**Parser for princess's grammar */
object Parser extends StandardTokenParsers {
  lexical.delimiters += ( ";", ",", "(", ")", "{", "}",
                          "+", "-", "->", "<->", "*",
                          "|", "&", "!", "=", "!=",
                          "<=", ">=", "<", ">", "\\")
  lexical.reserved += ("false", "true", "int", "nat", "inf")

  protected def makeEquiv(a: Formula, b: Formula) = Application(And, List(Application(Implies, List(a,b)), Application(Implies, List(b,a))))

  protected def expression: Parser[Formula] = rep1sep(expression1, "<->") ^^ ( lst => lst.reduceLeft(makeEquiv) )
  protected def expression1: Parser[Formula] = rep1sep(expression2, "->") ^^ ( lst => lst.reduceRight( (a,b) => Application(Implies, List(a,b)) ) ) //TODO the grammar says it should be left assoc, but right assoc makes more sense ?
  protected def expression2: Parser[Formula] = rep1sep(expression3, "|") ^^ ( lst => if (lst.size == 1) lst.head else Application(Or, lst) )
  protected def expression3: Parser[Formula] = rep1sep(expression4, "&") ^^ ( lst => if (lst.size == 1) lst.head else Application(And, lst) )

  protected def expression4: Parser[Formula] =
    ( "!" ~> expression4    ^^ ( e1 => Application(Not, List(e1)))
    | expression5
    )

  protected def expression5: Parser[Formula] =
    ( "true"                                ^^^ Literal(true)
    | "false"                               ^^^ Literal(false)
    | expression6 ~ (relSym ~ expression6).? ^^ { case e1 ~ Some(rel ~ e2) => Application(rel, List(e1, e2))
                                                  case e1 ~ None => e1 }
    )

  protected def expression6: Parser[Formula] =
    chainl1(
        expression7,
        expression7,
        ( "+" ^^^ ( (a: Formula, b: Formula) => Application(Plus, List(a,b)) )
        | "-" ^^^ ( (a: Formula, b: Formula) => Application(Minus, List(a,b)) )
        )
    )
  
  protected def expression7: Parser[Formula] = rep1sep(expression8, "*") ^^ ( lst => lst.reduceLeft(  (a,b) => Application(Times, List(a,b)) ))

  protected def expression8: Parser[Formula] =
    "-".? ~ expression9 ^^ { case Some(_) ~ Literal(l: Int) => Literal(-l).setType(Int)
                             case Some(_) ~ e => Application(Minus, List(Literal(0).setType(Int), e))
                             case None ~ e => e }
  
  protected def expression9: Parser[Formula] =
    ( ident                     ^^ ( id => Variable(id).setType(Int) )
    | numericLit                ^^ ( n => Literal(n.toInt).setType(Int) ) //TODO can overflow
    | "(" ~> expression <~ ")"
    )

  protected def relSym: Parser[InterpretedFct] =
    ( ">=" ^^^ Geq
    | "<=" ^^^ Leq
    | ">"  ^^^ Gt
    | "<"  ^^^ Lt
    | "="  ^^^ Eq
    | "!=" ^^^ Neq
    )

  def parseExpression(str: String) = {
    try {
      val tokens = new lexical.Scanner(str)
      val result = phrase(expression)(tokens)
      if (result.successful) {
        Some(result.get)
      } else {
        Logger("princess", LogError, "parsing error: " + result.toString)
        None
      }
    } catch { case err =>
      Logger("princess", LogError, "exception throw during parsing: " + err)
      None
    }
  }

}
