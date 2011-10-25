package picasso.frontend.basic

import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.combinator.syntactical._
import picasso.utils.IO

object BasicParser extends StandardTokenParsers {
  lexical.delimiters += (";", ",", "(", ")", "!", "?", "_", "=>", ":=")
  lexical.reserved += ( "begin", "end", "var", "val", "new",
                        "if", "then", "else", "true", "false",
                        "while", "foreach", "do", "yield", "in",
                        "select", "case", "initial")

  //TODO declaration of case classes ?

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

  //TODO allow some form of infix operation (=, !=)
  //TODO '!' as unary not
  //TODO functions with special meaning about sets ...
  def expr: Parser[Expression] = positioned(
      literal                                       ^^ ( lit => Value(lit) )
    | "_"                                           ^^^ Any
    | "(" ~> repsep(expr, ",") <~ ")"               ^^ ( lst => Tuple(lst) )
    | ident ~ opt("(" ~> repsep(expr, ",") <~ ")")  ^^ { case "newChannel" ~ Some(Nil) => NewChannel()
                                                         case id ~ Some(args) => Application(id, args)
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
    | ("new" ~> ident ~ ("(" ~> repsep(expr, ",") <~ ")"))  ^^ {
                                                        case id ~ args => Expr(Create(id, args))
                                                    }
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

  def actor: Parser[Actor] = positioned(
    ident ~ ("(" ~> repsep(ident, ",") <~")") ~ proc    ^^ { case id ~ params ~ body => Actor(id, params, body) }
  )

  //TODO more structured
  def initial: Parser[Expression] =
    "initial" ~> rep1sep(ident ~ ("(" ~> repsep(expr, ",") <~")"), ";")  ^^ (lst => Tuple(lst map {case id ~ args => Create(id, args)}))
    //The set of names can be inferred from the parameters of the actors.

  def system: Parser[(Seq[Actor], Expression)] =
    rep1(actor) ~ initial                          ^^ { case actors ~ init => (actors, init) }

  def apply(toParse: String) = {
    val tokens = new lexical.Scanner(toParse)
    phrase(system)(tokens)
  }

  def parseFile(fileName: String) = {
    apply(IO.readTextFile(fileName))
  }

}

