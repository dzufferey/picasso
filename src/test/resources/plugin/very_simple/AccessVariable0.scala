
class Access0(val init: Boolean) {
  var v1 = !init
}

object Main {

  def main(args: Array[String]) {
    val a0 = new Access0(true)
    assert(a0.init)
    assert(!a0.v1)
    a0.v1 = true
    assert(a0.v1)
    a0.v1 = false 
    assert(!a0.v1)
  }

}
