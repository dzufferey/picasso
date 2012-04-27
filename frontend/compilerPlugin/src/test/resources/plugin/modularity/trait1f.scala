
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

trait C extends Top {
  b = false
}

object Main {

  def main(args: Array[String]) {
    val t6 = new Top with A with C
    assert(!t6.b)
    t6.doSomething
    assert(t6.b)
  }

}
