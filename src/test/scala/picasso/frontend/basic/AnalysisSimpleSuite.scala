package picasso.frontend.basic

import org.scalatest._

class AnalysisSimpleSuite extends FunSuite {
  
  val testDir = "src/test/resources/basic/"

  def computeCover(fn: String) = {
    val a = Main.mkAnalysis(testDir + fn)
    val c = a.computeCover
    true
  }

  val files = List(
    "client-server.basic"
  )

  for (f <- files) { test("cover of " + f) { assert(computeCover(f)) } }

}
