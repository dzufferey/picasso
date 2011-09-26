package picasso.utils

import org.scalatest._

class LoggerSuite extends FunSuite {
     
  test("lazy evaluation of message with priority") {
    val logger = new Logger
    logger.setMinPriority(LogDebug)
    intercept[java.lang.RuntimeException] {
      logger("LoggerSuite", LogDebug, sys.error("should happen"))
    }
    logger.setMinPriority(LogCritical)
    logger("LoggerSuite", LogError, sys.error("should not happen"))
    logger.reset
    intercept[java.lang.RuntimeException] {
      logger("LoggerSuite", LogError, sys.error("should happen"))
    }
  }

  test("lazy evaluation of message with disallow && allow message") {
    val logger = new Logger
    intercept[java.lang.RuntimeException] {
      logger("LoggerSuite", LogNotice, sys.error("should happen"))
    }
    logger.disallow("LoggerSuite2")
    intercept[java.lang.RuntimeException] {
      logger("LoggerSuite", LogNotice, sys.error("should happen"))
    }
    logger.disallow("LoggerSuite")
    logger("LoggerSuite", LogInfo, sys.error("should not happen"))
    logger.allow("LoggerSuite")
    intercept[java.lang.RuntimeException] {
      logger("LoggerSuite", LogNotice, sys.error("should happen"))
    }
    logger.reset
    intercept[java.lang.RuntimeException] {
      logger("LoggerSuite2", LogNotice, sys.error("should happen"))
    }
  }

  test("logAndThrow") {
    val logger = new Logger
    intercept[java.lang.RuntimeException] {
      logger.logAndThrow("LoggerSuite", LogNotice, "should throw an exception")
    }
  }

}

