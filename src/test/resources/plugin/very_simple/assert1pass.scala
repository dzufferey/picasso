object Main {
  def main(args: Array[String]) {
    val b1 = scala.util.Random.nextBoolean()
    val b = true
    assert(b || b1)
  }
}
