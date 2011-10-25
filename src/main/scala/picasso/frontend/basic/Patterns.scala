package picasso.frontend.basic

sealed abstract class Pattern extends scala.util.parsing.input.Positional with Typed
abstract class SymPat extends Pattern with Sym

case class PatternLit(l: Literal) extends Pattern {
  setType(l.tpe)
  override def toString = l.toString
}

case object Wildcard extends Pattern {
  override def toString = "_"
}

case class PatternTuple(lst: List[Pattern]) extends Pattern {
  override def toString = lst.mkString("(", ", " ,")")
}

case class Case(uid: String, args: List[Pattern]) extends SymPat {
  override def toString = uid + args.mkString("(", ", " ,")")
}

//TODO binding ?
case class Ident(lid: String) extends SymPat {
  override def toString = lid
}

object Patterns {

  def lit2Lit(l: PatternLit): picasso.ast.Pattern = l.l match {
    case b @ Bool(_) => picasso.ast.PatternLit[Boolean](Literals.bool2Lit(b))
    case s @ StringVal(_) => picasso.ast.PatternLit[String](Literals.string2Lit(s))
  }
  def tuple2Tuple(t: PatternTuple): picasso.ast.PatternTuple = picasso.ast.PatternTuple(t.lst map pat2Pat)
  def case2Case(c: Case): picasso.ast.Case = picasso.ast.Case(c.uid, c.args map pat2Pat)
  def wc2WC = picasso.ast.Wildcard
  def id2Binding(id: Ident): picasso.ast.Binding = picasso.ast.Ident(Expressions.id2ID(ID(id.lid)))
  implicit def pat2Pat(p: Pattern): picasso.ast.Pattern = p match {
    case Wildcard => wc2WC
    case p @ PatternLit(_) => lit2Lit(p)
    case p @ PatternTuple(_) => tuple2Tuple(p)
    case p @ Case(_,_) => case2Case(p)
    case p @ Ident(_) => id2Binding(p)
  }
}
