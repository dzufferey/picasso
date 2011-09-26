
class Top {
  var b = true
  def doSomething: Unit = ()
}

trait B extends Top {
  override def doSomething: Unit = {
    super.doSomething
    b = false
  }
}

object Main {

  def main(args: Array[String]) {

    val t3 = new Top with B
    assert(t3.b)
    t3.doSomething
    assert(!t3.b)
    t3.doSomething
    assert(!t3.b)

  }

}
