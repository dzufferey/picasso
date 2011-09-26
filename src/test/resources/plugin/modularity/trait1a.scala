
class Top {
  var b = true
  def doSomething: Unit = ()
}

object Main {

  def main(args: Array[String]) {

    val t1 = new Top
    assert(t1.b)
    t1.doSomething
    assert(t1.b)

  }

}
