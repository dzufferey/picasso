package picasso.ast

import picasso.math.hol.{Bool => HBool, _}

//TODO that kind of thing is felated to the scala translation ...
//can we generalize it to a more flexible system ?
//-global makes senses (an easy shortcut),
//-local also (as you expect),
//-class is an artifact of the OO translation. (how to generalize or remove ?)
sealed abstract class AccessMode
case object LocalScope extends AccessMode //is in the current method
case object ClassScope extends AccessMode //is a class object
case object GlobalScope extends AccessMode //is a global ref

//TODO should Expression be typed ?
//basic types as uninterpreted, boolean, integer (interval), string, multiSet[type], channel[contract]
//everyting should be straightforward but the channel typing.
sealed abstract class Expression {
  def toStringRaw: String
  def ids: Set[ID]
}
case class Value[T](l: Literal[T]) extends Expression {
  override def toString = l.toString
  def toStringRaw = "Value("+l.toString+")"
  def ids = Set.empty[ID]
}
case class ID(id: Variable) extends Expression {
  override def toString = id.toString
  def toStringRaw = "ID" + id.toStringFull
  def toStringFull = id.toStringFull
  def ids = Set[ID](this)
  var accessMode: AccessMode = LocalScope
  def setMode(m: AccessMode): this.type = {
    accessMode = m
    this
  }
}
case class Application(fct: String, args: List[Expression]) extends Expression {
  def toStringRaw = "Application("+fct+","+args.map(_.toStringRaw).mkString("",",",")")
  override def toString = fct + args.mkString("(", ", " ,")")
  def ids = {
    val args = this match {
      case Create(_, args) => args
      case Application(_, args) => args
    }
    (Set.empty[ID] /: args)(_ ++ _.ids)
  }
}
//Tuple as Application ?
case class Tuple(values: List[Expression]) extends Expression {
  def toStringRaw = values.map(_.toStringRaw).mkString("Tuple(",",",")")
  override def toString = values.mkString("(", ", " ,")")
  def ids = (Set.empty[ID] /: values)(_ ++ _.ids)
}
case object Any extends Expression {
  def toStringRaw = toString
  def ids = Set.empty[ID]
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
  def unapply(e: Tuple): Boolean = e match {
    case Tuple(Nil) => true
    case _ => false
  }
}

object NewChannel {
  def apply() = Application("new-channel", Nil)
  def unapply(e: Application): Boolean = e match {
    case Application("new-channel", Nil) => true
    case _ => false
  }
}

object Create {
  //TODO what should be the type of Variable(name)
  def apply(name: String, args: List[Expression]) = Application("create", ID(Variable(name)) :: args)
  def unapply(e: Application): Option[(String, List[Expression])] = e match {
    case Application("create", ID(Variable(name)) :: args) => Some(name, args)
    case _ => None
  }
}

///////////////
//Collections//
///////////////

object EmptySet {
  def apply() = Application("set-new", Nil)
  def unapply(e: Application): Boolean = e match {
    case Application("set-new", Nil) => true
    case _ => false
  }
}

object SetIsEmpty {
  def apply(e: Expression) = Application("set-is-empty", List(e))
  def unapply(e: Application): Option[Expression] = e match {
    case Application("set-is-empty", List(e)) => Some(e)
    case _ => None
  }
}

object SetAdd {
  def apply(e1: Expression, e2: Expression) = Application("set-add", List(e1,e2))
  def unapply(e: Application): Option[(Expression,Expression)] = e match {
    case Application("set-add", List(e1,e2)) => Some((e1,e2))
    case _ => None
  }
}

object SetMinus {
  def apply(e1: Expression, e2: Expression) = Application("set-minus", List(e1,e2))
  def unapply(e: Application): Option[(Expression,Expression)] = e match {
    case Application("set-minus", List(e1,e2)) => Some((e1,e2))
    case _ => None
  }
}

//do not remove the chosen element from the set
object SetChoose {
  def apply(e: Expression) = Application("set-choose", List(e))
  def unapply(e: Application): Option[Expression] = e match {
    case Application("set-choose", List(e)) => Some(e)
    case _ => None
  }
}

//do remove the chosen element from the set (this operation is not side-effect free)
//it is a combination of SetChoose + SetMinus
object SetPick {
  def apply(e: Expression) = Application("set-pick", List(e))
  def unapply(e: Application): Option[Expression] = e match {
    case Application("set-pick", List(e)) => Some(e)
    case _ => None
  }
}

object SetCopy {
  def apply(e1: Expression) = Application("set-copy", List(e1))
  def unapply(e: Application): Option[Expression] = e match {
    case Application("set-copy", List(e)) => Some(e)
    case _ => None
  }
}


//TODO more extractors 
