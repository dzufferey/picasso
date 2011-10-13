package picasso.frontend

import org.scalatest._
import picasso.utils._
import picasso.model.dbp._

class DBPGraphsSuite extends FunSuite {
  
  val testDir = "src/test/resources/dbp_graph/"
  val logLevel = LogNotice
  val allowedLevel = LogDebug
  val disallowed = List("graph")

  //TODO use KM tree
  def computeCover(fileName: String) {
    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(allowedLevel)
    for(what <- disallowed) Logger.disallow(what)
    try  {
      val file = IO.readTextFile(testDir + fileName)
      DBPGraphParser(file) match {
        case Some((init, trs, traget)) =>
          val process = new DepthBoundedProcess(trs)
          Logger("DBPGraphsSuite", logLevel, Misc.docToString(process.toGraphviz("DBPGraph")) )
          val coverKM = DBPGraphs.computeCoverKM(init, trs)
          Logger("DBPGraphsSuite", logLevel, "coverKM: " + coverKM)
          //val coverSF = DBPGraphs.computeCoverSF(init, trs)
          //Logger("DBPGraphsSuite", logLevel, "coverSF: " + coverSF)
          //assert(coverKM == coverSF)
        case None =>
          Logger.logAndThrow("DBPGraphsSuite", LogError, "parsing of '" + file + "' failed")
      }
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
  
}
