object HelloWorld {

  def recPrint(str: String): Unit = {
    if(str == "") {
      println
    } else {
      print(str(0))
      recPrint(str.substring(1))
    }
  }
  def main(args: Array[String]) {
    recPrint("Hello, world!")
  }
}
