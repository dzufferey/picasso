object Main {
  def main(args: Array[String]) {
    val set = new scala.collection.mutable.ListBuffer[Boolean]()
    set += scala.util.Random.nextBoolean()
    set += scala.util.Random.nextBoolean()
    set += scala.util.Random.nextBoolean()
    set += scala.util.Random.nextBoolean()
    val res = for (b <- set) yield b ^ !b
    for (b <- res) assert(b)
  }
}
