
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
    val t1 = new Top{ def doSomething = () }
    assert(t1.b)
    t1.doSomething
    assert(t1.b)
    val t2 = new A{ }
    assert(t2.b)
    t2.doSomething
    assert(!t2.b)
    t2.doSomething
    assert(t2.b)
    val t3 = new B{ }
    assert(t3.b)
    t3.doSomething
    assert(!t3.b)
    t3.doSomething
    assert(!t3.b)
  }

}
