
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

object Main {

  def main(args: Array[String]) {

    val t2 = new Top with A
    assert(t2.b)
    t2.doSomething
    assert(!t2.b)
    t2.doSomething
    assert(t2.b)

  }

}
