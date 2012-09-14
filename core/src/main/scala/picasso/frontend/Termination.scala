package picasso.frontend

import picasso.utils._
import picasso.utils.report._
import picasso.model.dbp._
import picasso.model.integer.Program
import picasso.analysis._

class Termination[P <: picasso.model.dbp.DBCT](
    fileName: String,
    content: String,
    parse: String => Option[(DepthBoundedProcess[P], DepthBoundedConf[P], Option[DepthBoundedConf[P]])]
  ) extends AnalysisCommon[P]("Termination", fileName, content, parse)
{

  protected def runARMC(prog: Program) {
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      try {
        val armcProg = prog.printForARMC
        Logger("Termination", LogInfo, "ARMC program:\n" + armcProg)
        IO.writeInFile(file, armcProg)
        SysCmd.execRedirectToLogger(Array(Config.armcCmd, "live", file), None, "ARMC", LogNotice)
      } finally {
        SysCmd(Array("rm", file))
      }
    } else {
      Logger.logAndThrow("Termination", LogError, "cannot create temp file ("+code+"): " + err)
    }
  }

  protected def analysis(_process: DepthBoundedProcess[P], init: DepthBoundedConf[P], target: Option[DepthBoundedConf[P]]): Unit = {
    assert(target.isEmpty, "Termination analysis does not expect a target state")

    val intProgram = {
      val process = new DepthBoundedProcess( _process) with DBPTermination[P]
      val (_, _, p) = process.termination(init)
      p
    }

    if (Config.dumpArmc == "") {
      runARMC(intProgram)
    } else {
      Logger("Termination", LogInfo, "saving ARMC program in " + Config.dumpArmc)
      IO.writeInFile(Config.dumpArmc, intProgram.printForARMC(_))
    }
  }

}
