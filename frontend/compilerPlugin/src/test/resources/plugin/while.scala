object Main {
  def main(args: Array[String]) {
    try {
      assert(args.length >= 1)
      var elem = Integer.parseInt(args(0))
      var res = 0
      if (elem >= 0) {
        while (elem > 0) {
          res += elem
          elem -= 1
        }
      } else {
        do {
          res -= elem
          elem += 1
        } while (elem < 0) 
      }
      println("res: " + res)
    } catch {
       case e: NumberFormatException => 
         println("Usage: scala Main <n1>")
    }
  }
}
