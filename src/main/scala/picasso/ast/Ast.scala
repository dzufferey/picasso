package picasso.ast

import picasso.math.hol.{Bool => HBool, _}

sealed abstract class AccessMode
case object LocalScope extends AccessMode //is in the current method
case object ClassScope extends AccessMode //is a class object
case object GlobalScope extends AccessMode //is a global ref

//TODO should Expression be typed ?
//basic types as uninterpreted, boolean, integer (interval), string, multiSet[type], channel[contract]
//everyting should be straightforward but the channel typing.
sealed abstract class Expression {
  def toStringRaw: String
}
case class Value[T](l: Literal[T]) extends Expression {
  override def toString = l.toString
  def toStringRaw = "Value("+l.toString+")"
}
case class ID(id: Variable) extends Expression {
  override def toString = id.toString
  def toStringRaw = "ID" + id.toStringFull
  def toStringFull = id.toStringFull
  var accessMode: AccessMode = LocalScope
  def setMode(m: AccessMode): this.type = {
    accessMode = m
    this
  }
}
case class Application(fct: String, args: List[Expression]) extends Expression {
  def toStringRaw = "Application("+fct+","+args.map(_.toStringRaw).mkString("",",",")")
  override def toString = fct + args.mkString("(", ", " ,")")
}
//Tuple as Application ?
case class Tuple(values: List[Expression]) extends Expression {
  def toStringRaw = values.map(_.toStringRaw).mkString("Tuple(",",",")")
  override def toString = values.mkString("(", ", " ,")")
}
case object Any extends Expression {
  def toStringRaw = toString
}

object Bool {
  def apply(b: Boolean) = {
    val lit = Literal[Boolean](b)
    lit.tpe = HBool
    lit
  }
  def unapply(l: Literal[Any]): Option[Boolean] = l match {
    case Literal(true) => Some(true)
    case Literal(false) => Some(false)
    case _ => None
  }
}

object StringVal {
  def apply(s: String) = {
    val lit = Literal[String](s)
    lit.tpe = String
    lit
  }
  def unapply(l: Literal[Any]): Option[String] = l match {
    case Literal(str: String) => Some(str)
    case _ => None
  }
}

object Unit {
  def apply() = Tuple(Nil)
  def unapply(e: Expression): Boolean = e match {
    case Tuple(Nil) => true
    case _ => false
  }
}

object NewChannel {
  def apply() = Application("new-channel", Nil)
  def unapply(e: Expression): Boolean = e match {
    case Application("new-channel", Nil) => true
    case _ => false
  }
}

object Create {
  //TODO what should be the type of Variable(name)
  def apply(name: String, args: List[Expression]) = Application("create", ID(Variable(name)) :: args)
  def unapply(e: Expression): Option[(String, List[Expression])] = e match {
    case Application("create", ID(Variable(name)) :: args) => Some(name, args)
    case _ => None
  }
}

///////////////
//Collections//
///////////////

object EmptySet {
  def apply() = Application("set-new", Nil)
  def unapply(e: Expression): Boolean = e match {
    case Application("set-new", Nil) => true
    case _ => false
  }
}

object SetIsEmpty {
  def apply(e: Expression) = Application("set-is-empty", List(e))
  def unapply(e: Expression): Option[Expression] = e match {
    case Application("set-is-empty", List(e)) => Some(e)
    case _ => None
  }
}

object SetAdd {
  def apply(e1: Expression, e2: Expression) = Application("set-add", List(e1,e2))
  def unapply(e: Expression): Option[(Expression,Expression)] = e match {
    case Application("set-add", List(e1,e2)) => Some((e1,e2))
    case _ => None
  }
}

object SetMinus {
  def apply(e1: Expression, e2: Expression) = Application("set-minus", List(e1,e2))
  def unapply(e: Expression): Option[(Expression,Expression)] = e match {
    case Application("set-minus", List(e1,e2)) => Some((e1,e2))
    case _ => None
  }
}

//do not remove the chosen element from the set
object SetChoose {
  def apply(e: Expression) = Application("set-choose", List(e))
  def unapply(e: Expression): Option[Expression] = e match {
    case Application("set-choose", List(e)) => Some(e)
    case _ => None
  }
}

//do remove the chosen element from the set (this operation is not side-effect free)
//it is a combination of SetChoose + SetMinus
object SetPick {
  def apply(e: Expression) = Application("set-pick", List(e))
  def unapply(e: Expression): Option[Expression] = e match {
    case Application("set-pick", List(e)) => Some(e)
    case _ => None
  }
}

//TODO more extractors 

//TODO the bind element in pattern is probably a better idea rather than Ident
sealed abstract class Pattern {
  def toStringRaw: String
}
case class PatternLit[T](l: Literal[T]) extends Pattern {
  def toStringRaw = "PatternLit("+l+")"
  override def toString = l.toString
}
case class PatternTuple(lst: List[Pattern]) extends Pattern {
  def toStringRaw = lst.map(_.toStringRaw).mkString("PatternTuple(", ", " ,")")
  override def toString = lst.mkString("(", ", " ,")")
}
case class Case(uid: String, args: List[Pattern]) extends Pattern {
  def toStringRaw = "Case(" + uid + args.map(_.toStringRaw).mkString(", ", ", ", ")")
  override def toString = uid + args.mkString("(", ", " ,")")
}
case object Wildcard extends Pattern {
  def toStringRaw = "Wildcard"
  override def toString = "_"
}
case class Binding(v: ID, p: Pattern) extends Pattern {
  def toStringRaw = "Binding("+v.toStringRaw+" @ "+p.toStringRaw+")"
  override def toString = p match {
    case Wildcard => v.toString
    case _ => v + " @ " + p
  }
}

object Ident {
  //def apply(lid: String) = Binding(Variable(lid), Wildcard)
  def apply(v: ID) = Binding(v, Wildcard)
  def unapply(p: Pattern): Option[ID] = p match {
    case Binding(v, Wildcard) => Some(v)
    case _ => None
  }
}

sealed abstract class Process {
  def toStringRaw: String
}
case class Block(stmts: List[Process]) extends Process {
  def toStringRaw = stmts.map(_.toStringRaw).mkString("Block(", ", ", ")")
  override def toString = stmts.mkString("{","; ","}") 
}
case class Affect(id: ID, value: Expression) extends Process {
  def toStringRaw = "Affect("+id.toStringRaw+","+value.toStringRaw+")"
  override def toString = id + " := " + value
}
case class Expr(e: Expression) extends Process {
  def toStringRaw = "Expr("+e.toStringRaw+")"
  override def toString = e.toString
}
case class Send(dest: Expression, content: Expression) extends Process {
  def toStringRaw = "Send("+dest.toStringRaw+","+content.toStringRaw+")"
  override def toString = dest + "!" + content
}
case class Receive(src: Expression, pat: Pattern) extends Process {
  def toStringRaw = "Receive("+src.toStringRaw+","+pat.toStringRaw+")"
  override def toString = src + "?" + pat
}

object Skip {
  def apply() = Expr(Unit())
  def unapply(p: Process): Boolean = p match {
    case Expr(Unit()) => true
    case _ => false
  }
}

object Zero {
  def apply() = Block(Nil)
  def unapply(p: Process): Boolean = p match {
    case Block(Nil) => true
    case _ => false
  }
}
object Assume {
  def apply(e: Expression) = Expr(Application("assume", List(e)))
  def unapply(p: Process): Option[Expression] = p match {
    case Expr(Application("assume", List(e))) => Some(e)
    case _ => None
  }
}
object Assert {
  def apply(e: Expression) = Expr(Application("assert", List(e)))
  def unapply(p: Process): Option[Expression] = p match {
    case Expr(Application("assert", List(e))) => Some(e)
    case _ => None
  }
}

//TODO define a normal form on the program

import scala.collection.immutable.Set
import scala.collection.immutable.Map
import scala.text.Document
import picasso.graph._
import picasso.utils.Misc

//TODO rather than Process on the edges, should have some guarded command language
/** An agent ...
 *  TODO params should be a list of pattern ?
 *  @param id the name of the agent kind
 *  @param params the parameters for the agent creation
 *  @param transitions transitions
 *  @param init the initial location
 *  @param target the exit locations
 */
class AgentDefinition[PC](val id: String, val params: List[ID], val cfa: Automaton[GT.ELGT{type V = PC; type EL = Process}]){

  def this(id: String, params: List[ID], transition: Map[PC,Map[Process,Set[PC]]], init: PC, target: Set[PC]) = 
    this(id, params, new Automaton[GT.ELGT{type V = PC; type EL = Process}](transition, init, target))


  def morphFull[PC2](nodes: PC => PC2, edges: Process => Process): AgentDefinition[PC2] = {
    new AgentDefinition(id, params, cfa.morphFull[GT.ELGT{type V = PC2; type EL = Process}](nodes, edges))
  }
  
  def toGraphviz(name: String, prefix: String, idPrefix: String): Document = {
    import scala.text.Document._
    val inBody =
      if ((name startsWith "cluster_") && (prefix == "subgraph"))
        text("label = " + Misc.quote(id + params.mkString("(",",",")")) + ";")
      else
        empty
    cfa.toGraphvizFull(name, prefix, inBody, idPrefix)._1
  }
  
  override def toString = "agent: " + id + params.mkString("(",",",")") + "\n" + cfa

}

// define transitions (matching I/O prefixes, internal transitions, ...)
// reduction rules ...
