
trait Top {

  var b = true

  def doSomething: Unit

}

object Main {

  def main(args: Array[String]) {
    val t1 = new Top{ def doSomething = () }
    assert(t1.b)
    t1.doSomething
    assert(t1.b)
  }

}
