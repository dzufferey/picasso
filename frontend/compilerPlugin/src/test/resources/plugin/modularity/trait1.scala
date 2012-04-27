
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

trait C extends Top {
  b = false
}

object Main {

  def main(args: Array[String]) {

    val t1 = new Top
    assert(t1.b)
    t1.doSomething
    assert(t1.b)

    val t2 = new Top with A
    assert(t2.b)
    t2.doSomething
    assert(!t2.b)
    t2.doSomething
    assert(t2.b)

    val t3 = new Top with B
    assert(t3.b)
    t3.doSomething
    assert(!t3.b)
    t3.doSomething
    assert(!t3.b)

    val t4 = new Top with A with B
    assert(t4.b)
    t4.doSomething
    assert(!t4.b)
    t4.doSomething
    assert(!t4.b)

    val t5 = new Top with B with A
    assert(t5.b)
    t5.doSomething
    assert(t5.b)
    t5.doSomething
    assert(t5.b)

    val t6 = new Top with A with C
    assert(!t6.b)
    t6.doSomething
    assert(t6.b)
  }

}
