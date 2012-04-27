
class Bool1(val init: Boolean) {

  var v1 = !init

  def flip = v1 = !v1
}

class Bool2(i: Boolean) extends Bool1(i) {
  
  val v2 = true
  flip

}

object Main {

  def main(args: Array[String]) {
    val b1 = new Bool1(true)
    val b2 = new Bool2(false)
    assert(b1.v1 != b2.v2)
  }

}
