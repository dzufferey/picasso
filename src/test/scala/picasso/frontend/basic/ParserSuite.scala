package picasso.frontend.basic

import org.scalatest._
import picasso.utils._

class ParserSuite extends FunSuite {
  
  val testDir = "src/test/resources/basic/"

  def tryParse(fileName: String) = {
    val file = IO.readTextFile(testDir + fileName)
    BasicParser(file)
  }

  test("should parse") {
    val files = List(
      "client-server.basic"
    )
    for (f <- files) {
      val result = tryParse(f)
      assert(result.successful, f + " " + result.toString)
    }
  }

}
