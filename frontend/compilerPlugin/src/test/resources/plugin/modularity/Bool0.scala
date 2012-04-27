
class Bool0(val init: Boolean) {
  var v1 = !init
  def flip = v1 = !v1
}

object Main {

  def main(args: Array[String]) {
    val b1 = new Bool0(true)
    b1.flip
    assert(b1.v1 == true)
  }

}
