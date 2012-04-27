package picasso.frontend.dbpGraph

import org.scalatest._
import picasso.utils._
import picasso.model.dbp._

class DBPGraphsSuite extends FunSuite {
  
  val testDir = "core/src/test/resources/dbp_graph/"
  val logLevel = LogNotice
  val allowedLevel = LogDebug
  val disallowed = List("graph", "DBP")

  def computeCover(fileName: String) {
    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(allowedLevel)
    for(what <- disallowed) Logger.disallow(what)
    try  {
      val args = Array.ofDim[String](1)
      args(0) = testDir + fileName
      Main.main(args)
    } finally {
      Logger.setMinPriority(previousLog)
      for(what <- disallowed) Logger.allow(what)
    }
  }

  test("simple example from the paper") {
    computeCover("simple_omega_2.dbp")
  }
  
  //test("Petruchio: platoon") {
  //  computeCover("platoonFiniteHandlerPoly.dbp")
  //}
  
  test("Petruchio: clientServerNoFCP") {
    computeCover("clientServerNoFCP.dbp")
  }
  
  test("Petruchio: clientServer2s2c") {
    computeCover("clientServer2s2c.dbp")
  }
  
  //test("Petruchio: phone") {
  //  computeCover("phone.dbp")
  //}

  test("Petruchio: gsm") {
    computeCover("gsm.dbp")
  }
  
  test("simple example non-blocking") {
    computeCover("simple_non_blocking.dbp")
  }
  
  test("simple example non-blocking 2") {
    computeCover("simple_non_blocking_2.dbp")
  }

}
