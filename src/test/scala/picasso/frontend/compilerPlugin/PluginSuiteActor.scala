package picasso.frontend.compilerPlugin

import org.scalatest._
import PluginSuiteCommon._

class PluginSuiteActor extends FunSuite {

  test("trivial test: Actor0") {
    runPluginCover(List("Actor0"))
  }
  
  test("trivial test: PingPong") {
    runPluginCover(List("PingPong"))
  }

}
