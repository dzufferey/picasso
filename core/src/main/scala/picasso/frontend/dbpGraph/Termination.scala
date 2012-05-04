package picasso.frontend.dbpGraph

import picasso.utils._
import picasso.utils.report._
import picasso.model.dbp._
import picasso.model.integer.Program
import picasso.analysis._

class Termination(fileName: String, content: String) extends AnalysisCommon("Termination", fileName, content) {

  protected def runARMC(prog: Program) {
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      try {
        Logger("Termination", LogInfo, "ARMC program:\n" + prog.printForARMC)
        IO.writeInFile(file, prog.printForARMC)
        SysCmd.execRedirectToLogger(Array(Config.armcCmd, "live", file), None, "ARMC", LogNotice)
      } finally {
        SysCmd(Array("rm", file))
      }
    } else {
      Logger.logAndThrow("Termination", LogError, "cannot create temp file ("+code+"): " + err)
    }
  }

  protected def analysis[P <: picasso.model.dbp.DBCT](_process: DepthBoundedProcess[P], init: DepthBoundedConf[P], target: Option[DepthBoundedConf[P]]): Unit = {
    assert(target.isEmpty, "Termination analysis does not expect a target state")

    val intProgram =
      if (Config.useTree) {
        val process = new DepthBoundedProcess( _process) with DBPTermination[P]
        val (_, p) = process.termination(init)
        p
      } else {
        val process = new DepthBoundedProcess( _process) with DBPTermination2[P]
        val (_, _, p) = process.termination(init)
        p
      }

    runARMC(intProgram)
  }

}
