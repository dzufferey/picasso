package picasso.frontend.basic

import org.scalatest._

class TyperSuite extends FunSuite {
  
  val testDir = "src/test/resources/basic/"

  test("should type") {
    val files = List(
      "client-server.basic"
    )
    for (f <- files) {
      val result = BasicParser.parseFile(testDir + f)
      assert(result.successful)
      val typed = typer.Typer(result.get._1)
      assert(typed.success, typed.toString)
    }
  }

}
