package picasso.frontend.basic

object Symbol {
  var idCounter = 0

  def freshId = {
    idCounter += 1
    idCounter
  }

  def apply(name: String) = TermSymbol(name)
}

sealed abstract class Symbol extends Typed {

  val id = Symbol.freshId

  //TODO equality on id
  override def equals(x: Any) = x match {
    case x: Symbol => x.id == id
    case _ => false
  }

  override def hashCode() = id.hashCode()

}

case object NoSymbol extends Symbol {}

case object ErrorSymbol extends Symbol {}

case class TermSymbol(name: String) extends Symbol {
  //TODO
  override def toString = name + "#" + id
}

trait Sym {
  var symbol: Symbol = NoSymbol
  def setSymbol(s: Symbol): this.type = {
    symbol = s
    this
  }
}
