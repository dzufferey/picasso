package picasso.frontend.compilerPlugin

import org.scalatest._
import picasso.utils.{LogDebug, Logger}
import PluginSuiteCommon._

class PluginSuiteModularity extends FunSuite {
  
  test("trivial test: Bool0") {
    runPluginCover(List("modularity/Bool0"))
  }

  test("trivial test: Bool1") {
    runPluginCover(List("modularity/Bool1"))
  }

  test("trivial test: trait0a") {
    runPluginCover(List("modularity/trait0a"))
  }

  test("trivial test: trait0b") {
    runPluginCover(List("modularity/trait0b"))
  }
  
  test("trivial test: trait0c") {
    runPluginCover(List("modularity/trait0c"))
  }
  
  //test("trivial test: trait0") {
  //  runPluginCover(List("modularity/trait0"))
  //}

  test("trivial test: trait1a") {
    runPluginCover(List("modularity/trait1a"))
  }

  test("trivial test: trait1b") {
    runPluginCover(List("modularity/trait1b"))
  }

  test("trivial test: trait1c") {
    runPluginCover(List("modularity/trait1c"))
  }

  test("trivial test: trait1d") {
    runPluginCover(List("modularity/trait1d"))
  }

  test("trivial test: trait1e") {
    runPluginCover(List("modularity/trait1e"))
  }

  test("trivial test: trait1f") {
    runPluginCover(List("modularity/trait1f"))
  }

  //test("trivial test: trait1") {
  //  runPluginCover(List("modularity/trait1"))
  //}
}
