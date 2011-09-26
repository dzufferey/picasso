package picasso.frontend.compilerPlugin

import org.scalatest._
import picasso.utils.{LogDebug, Logger}
import PluginSuiteCommon._

class PluginSuiteVeryShort extends FunSuite {
  
  //TODO then what should be the check performed ?
  // - does not crash
  // - check that the transformations are idenpotent
  // - check for correctness of the transformation.
  //    how to do this automatically ? 
  //    it is possible for instance to check that there are no more nested classes.
  //    but for the real functional correctness, manual inspection seems the simplest.

  test("trivial test: hello") {
    runPluginCover(List("very_simple/hello"))
  }

  test("trivial test: hello2") {
    runPluginCover(List("very_simple/hello2"))
  }
  
  test("trivial test: assert0pass") {
    assert(!runPluginError(List("very_simple/assert0pass")))
  }
  
  test("trivial test: assert0fail") {
    assert(runPluginError(List("very_simple/assert0fail")))
  }

  test("trivial test: assert1pass") {
    assert(!runPluginError(List("very_simple/assert1pass")))
  }
  
  test("trivial test: assert1fail") {
    assert(runPluginError(List("very_simple/assert1fail")))
  }

  test("trivial test: Create0") {
    runPluginCover(List("very_simple/Create0"))
    assert(!runPluginError(List("very_simple/Create0")))
  }

  test("trivial test: AccessVariable0") {
    runPluginCover(List("very_simple/AccessVariable0"))
  }

  test("trivial test: AccessVariable1") {
    runPluginCover(List("very_simple/AccessVariable1"))
  }
  
  test("trivial test: boolOp0") {
    runPluginCover(List("very_simple/boolOp0"))
    assert(!runPluginError(List("very_simple/boolOp0")))
  }

  test("trivial test: global0") {
    assert(runPluginError(List("very_simple/global0")))
  }

}
