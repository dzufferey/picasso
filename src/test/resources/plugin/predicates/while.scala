import picasso.frontend.compilerPlugin.Annotations._

object Main {

  var x = 1000

  @Predicate
  val pred1 = x > 0
  @Predicate
  val pred2 = x < 0

  def main(args: Array[String]) {
    while (x > 0) {
      x -= 1
    }
    assert(x == 0)
  }

}
