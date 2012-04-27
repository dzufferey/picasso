
class Top {
  var b = true
  def doSomething: Unit = ()
}

trait A extends Top {
  override def doSomething: Unit = {
    super.doSomething
    b = !b
  }
}

trait B extends Top {
  override def doSomething: Unit = {
    super.doSomething
    b = false
  }
}

object Main {

  def main(args: Array[String]) {

    val t4 = new Top with A with B
    assert(t4.b)
    t4.doSomething
    assert(!t4.b)
    t4.doSomething
    assert(!t4.b)

  }

}
