object Main {
  def main(args: Array[String]) {
    try {
      assert(args.length >= 1)
      val elem = Integer.parseInt(args(0))
      if (elem >= 0) {
        println("Positive number")
      } else {
        println("Negative number")
      }
    } catch {
       case e: NumberFormatException => 
         println("Usage: scala Main <n1>")
    }
  }
}
