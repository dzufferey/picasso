package picasso.frontend.basic

import org.scalatest._
import picasso.utils._

class AnalysisSimpleSuite extends FunSuite {
  
  val testDir = "src/test/resources/basic/"

  def computeCover(fn: String) = {
    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(LogInfo)
    Logger.disallow("graph")
    try {
      val a = Main.mkAnalysis(testDir + fn)
      val c = a.computeCover
      true
    } finally {
      Logger.setMinPriority(previousLog)
      Logger.allow("graph")
    }
  }

  val files = List(
    "pi_akka_1.basic",
    "pi_akka_2.basic",
    "pi_akka_4.basic",
    "client-server.basic",
    "round_robin.basic"
  )

  for (f <- files) { test("cover of " + f) { assert(computeCover(f)) } }

}
