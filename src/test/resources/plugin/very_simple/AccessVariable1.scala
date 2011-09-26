
class Access1(val init: Boolean) {
  var v1 = init
}

object Main {

  def main(args: Array[String]) {
    val a1 = new Access1(true)
    assert(a1.init)
    assert(a1.v1)
    a1.v1 = true
    assert(a1.v1)
    a1.v1 = false 
    assert(!a1.v1)
  }

}
