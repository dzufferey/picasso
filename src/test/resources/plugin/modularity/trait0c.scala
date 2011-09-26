
trait Top {

  var b = true

  def doSomething: Unit

}

trait A extends Top {

  def doSomething = b = !b

}

trait B extends A {

  override def doSomething = b = false

}

object Main {

  def main(args: Array[String]) {
    val t3 = new B{ }
    assert(t3.b)
    t3.doSomething
    assert(!t3.b)
    t3.doSomething
    assert(!t3.b)
  }

}
