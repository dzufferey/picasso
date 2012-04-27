package picasso.frontend.compilerPlugin

import org.scalatest._
import picasso.utils.{LogDebug, Logger}
import PluginSuiteCommon._

class PluginSuiteCollection extends FunSuite {
  
  test("trivial test: forYield") {
    runPluginCover(List("forYield"))
  }
  
  test("trivial test: collection0") {
    runPluginCover(List("collection0"))
  }
  
  test("trivial test: collection1") {
    runPluginCover(List("collection1"))
  }
  
}
