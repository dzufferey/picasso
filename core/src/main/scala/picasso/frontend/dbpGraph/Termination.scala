package picasso.frontend.dbpGraph

import picasso.utils._
import picasso.utils.report._
import picasso.model.dbp._
import picasso.analysis.DBPTermination

class Termination(fileName: String, content: String) extends AnalysisCommon("Termination", fileName, content) {

  protected def analysis[P <: picasso.model.dbp.DBCT](_process: DepthBoundedProcess[P], init: DepthBoundedConf[P], target: Option[DepthBoundedConf[P]]): Unit = {
    assert(target.isEmpty) //TODO error msg

    val process = new DepthBoundedProcess( _process) with DBPTermination[P]

    val(tree, intProgram) = process.termination(init)

    println(intProgram.printForARMC)
    //println("----------------------")
    //println(intProgram.printForQARMC)

    sys.error("TODO")
  }

}
