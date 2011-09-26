object Main {
  def main(args: Array[String]) {
    try {
      val elems = args map Integer.parseInt
      println("The sum of my arguments is: " + elems.foldRight(0) (_ + _))
    } catch {
       case e: NumberFormatException => 
         println("Usage: scala Main <n1> <n2> ... ")
    }
  }
}

