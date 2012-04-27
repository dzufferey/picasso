
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

    val t5 = new Top with B with A
    assert(t5.b)
    t5.doSomething
    assert(t5.b)
    t5.doSomething
    assert(t5.b)
  }

}
