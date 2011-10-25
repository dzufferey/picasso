package picasso.frontend.basic

import org.scalatest._

class ParserSuite extends FunSuite {
  
  val testDir = "src/test/resources/basic/"

  test("should parse") {
    val files = List(
      "client-server.basic"
    )
    for (f <- files) {
      val result = BasicParser.parseFile(testDir + f)
      assert(result.successful, f + " " + result.toString)
    }
  }

}
