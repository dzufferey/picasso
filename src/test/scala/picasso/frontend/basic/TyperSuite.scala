package picasso.frontend.basic

import org.scalatest._
import picasso.utils._

class TyperSuite extends FunSuite {
  
  val testDir = "src/test/resources/basic/"

  test("should type") {
    val files = List(
      "client-server.basic",
      "client-server-with-TO.basic",
      "round_robin_2.basic",
      "round_robin_4.basic",
      "pi_akka_1.basic",
      "pi_akka_2.basic",
      "pi_akka_4.basic",
      "scala-ping-pong.basic",
      "scala-genericComputeServer.basic",
      "scala-liftChatLike-polling-noLogger-noExit.basic",
      "scala-liftChatLike-polling-noLogger.basic",
      "scala-liftChatLike-polling.basic",
      "collection_typing.basic"
    )

    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(LogInfo)
    try {
      for (f <- files) {
        val result = BasicParser.parseFile(testDir + f)
        assert(result.successful, result)
        val typed = typer.Typer(result.get._1)
        assert(typed.success, typed.toString)
        //Console.println(typed.toString)
      }
    } finally {
      Logger.setMinPriority(previousLog)
    }
  }

}
