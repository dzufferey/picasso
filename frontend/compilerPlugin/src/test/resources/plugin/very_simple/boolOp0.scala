object Main {
  def main(args: Array[String]) {
    val b1 = scala.util.Random.nextBoolean()
    val b2 = b1 && true
    val b3 = b1 || false
    val b4 = b1 && !b1
    val b5 = b1 || !b1
    assert(b2 == b1)
    assert(b3 == b1)
    assert(!(b1 ^ b1))
    assert(!b4)
    assert(b5)
    assert(b4 != b5)
    assert(b4 ^ b5)
  }
}
