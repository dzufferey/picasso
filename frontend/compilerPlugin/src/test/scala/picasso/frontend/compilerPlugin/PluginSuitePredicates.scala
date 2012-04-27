package picasso.frontend.compilerPlugin

import org.scalatest._
import PluginSuiteCommon._

class PluginSuitePredicates extends FunSuite {

  val dir = "predicates/"

  test("parsing @Predicate"){
    runPluginParse(List(dir + "while"))
  }

}
