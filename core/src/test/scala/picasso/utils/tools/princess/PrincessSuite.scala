package picasso.utils.tools.princess

import org.scalatest._
import picasso.utils._

class PrincessSuite extends FunSuite {
  
  val testDir = "core/src/test/resources/princess/"
  val allowedLevel = LogDebug

  def runQE(fn: String) {
    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(allowedLevel)
    try  {
      val fullName = testDir + fn
      Princess.eliminateQuantifiersFile(fullName) match {
        case Some(f) =>
          Logger("princess", LogInfo, "princess returned:")
          Logger("princess", LogInfo, Printer(_, f))
        case None => Logger("princess", LogInfo, "princess returned None.")
      }
    } finally {
      Logger.setMinPriority(previousLog)
    }
  }

  def runValid(fn: String) = {
    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(allowedLevel)
    try  {
      val fullName = testDir + fn
      Princess.isValidFile(fullName)
    } finally {
      Logger.setMinPriority(previousLog)
    }
  }
  
  test("Princess: test 1") {
    runQE("test_1.pri")
  }

  test("Princess: test 2") {
    runQE("test_2.pri")
  }

  test("Princess: valid 1") {
    assert(runValid("valid_1.pri") == Some(true))
  }
  
  test("Princess: valid 2") {
    assert(runValid("valid_2.pri") == Some(true))
  }


  test("Princess: invalid 1") {
    assert(runValid("invalid_1.pri") == Some(false))
  }
  
  test("Princess: invalid 2") {
    assert(runValid("invalid_2.pri") == Some(false))
  }
  
  test("Princess: invalid 3") {
    assert(runValid("invalid_3.pri") == Some(false))
  }

}
