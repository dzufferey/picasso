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
      val report = Main.analyse(testDir + fn)
      true
    } finally {
      Logger.setMinPriority(previousLog)
      Logger.allow("graph")
    }
  }

  val files = List(
    //"pi_akka_1.basic",
    //"pi_akka_2.basic",
    //"pi_akka_4.basic",
    "client-server.basic",
    "client-server-with-TO.basic",
    "scala-ping-pong.basic",
    "scala-genericComputeServer.basic",
    "scala-liftChatLike-polling-noLogger-noExit.basic",
    //"scala-liftChatLike-polling-noLogger.basic",
    //"scala-liftChatLike-polling.basic",
    "round_robin_2.basic",
    "round_robin_4.basic"
  )

  for (f <- files) { test("cover of " + f) { assert(computeCover(f)) } }

}
