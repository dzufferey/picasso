
object Global {

  def fail = assert(false)

}

object Main {
  def main(args: Array[String]) {
    Global.fail
  }
}
