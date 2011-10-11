package picasso.frontend.basic
import picasso.ast.basic._

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.combinator.syntactical._

object BasicParser extends StandardTokenParsers {
  lexical.delimiters += ("begin", "end", ";", ",")
  lexical.reserved += (":=", "var", "val", "if", "then", "else", "while", "foreach", "do", "yield", "in", "!", "?", "_", "=>", "*", "select", "case")

  def literal: Parser[Literal] = positioned(
      "true"                                        ^^^ Bool(true)
    | "false"                                       ^^^ Bool(false)
    //| numericLit                                    ^^ ( int => Integer(int.toInt) )
    | stringLit                                     ^^ ( str => StringVal(str) )
    )

  def pattern: Parser[Pattern] = positioned(
      literal                                       ^^ ( lit => PatternLit(lit) )
    | "(" ~> repsep(pattern, ",") <~ ")"            ^^ ( lst => PatternTuple(lst) )
    | ident ~ opt("(" ~> repsep(pattern, ",") <~ ")")  ^^ { case id ~ Some(args) => Case(id, args)
                                                            case id ~ None => Ident(id) }
    )

  def expr: Parser[Expression] = positioned(
      literal                                       ^^ ( lit => Value(lit) )
    | "*"                                           ^^^ Any
    | "(" ~> repsep(expr, ",") <~ ")"               ^^ ( lst => Tuple(lst) )
    | ident ~ opt("(" ~> repsep(expr, ",") <~ ")")  ^^ { case id ~ Some(args) => Application(id, args)
                                                         case id ~ None => ID(id) }
    )

  def cases: Parser[(Expression,Pattern,Process)] =
    ("case" ~> expr) ~ ("?" ~> pattern) ~ ("=>" ~> proc) ^^ {case a ~ b ~ c => (a,b,c)}

  def proc: Parser[Process] = positioned(
      "begin" ~> repsep(proc, ";") <~ "end"         ^^ ( stmts => Block(stmts))
    | ("var" ~> ident) ~ (":=" ~> expr)             ^^ { case id ~ value => Declaration(id, true, value) }
    | ("val" ~> ident) ~ (":=" ~> expr)             ^^ { case id ~ value => Declaration(id, false, value) }
    | ident ~ (":=" ~> expr)                        ^^ { case id ~ value => Affect(id, value) }
    | expr ~ ("!" ~> expr)                          ^^ { case dest ~ value => Send(dest, value) }
    | expr                                          ^^ ( e => Expr(e) )
    | "select" ~> rep1(cases)                       ^^ ( cases => Receive(cases))
    | ("if" ~> expr) ~ ("then" ~> proc) ~ opt("else" ~> proc) ^^ {
                                                         case e ~ tr ~ Some(fa) => ITE(e,tr,fa)
                                                         case e ~ tr ~ None => ITE(e,tr,Expr(Unit()))
                                                       }
    | ("while" ~> expr) ~ ("do" ~> proc)            ^^ { case cond ~ body => While(cond, body) }
    | ("foreach" ~> ident) ~ ("in" ~> expr) ~ ("do" ~> proc) ~ opt(("yield" ~> ident) ~ ("in" ~> ident)) ^^ {
                                                      case x ~ set ~ body ~ None => ForEach(x, set, body)
                                                      case x ~ setX ~ body ~ Some(y ~ setY) => ForEachYield(x, setX, y, setY, body)
                                                    }
    )

  //TODO actor definition
  //TODO init configuration: List of names + list of agents with parameters (lit or names)

  //example
  def main(args: Array[String]) {
    val tokens = new lexical.Scanner(args(0))
    println(args(0))
    println(phrase(proc)(tokens))
  }
}

