
class Create0(val init: Boolean) {
}

object Main {

  def main(args: Array[String]) {
    val b1 = new Create0(true)
    assert(b1.init)
  }

}
