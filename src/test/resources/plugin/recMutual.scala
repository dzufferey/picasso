object HelloWorld {

  def recPrint(str: String): Unit = {
    if(str == "") println
    else charAndSplit(str)
  }

  def charAndSplit(str: String): Unit = {
    print(str(0))
    recPrint(str.substring(1))
  }

  def main(args: Array[String]) {
    recPrint("Hello, world!")
  }
}
