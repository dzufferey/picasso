package picasso.utils.tools.armc

import picasso.model.integer._
import picasso.utils._

object ARMC {

  def apply(prog: Program) {
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      try {
        val armcProg = prog.printForARMC
        Logger("ARMC", LogInfo, "program:\n" + armcProg)
        IO.writeInFile(file, armcProg)
        SysCmd.execRedirectToLogger(Array(Config.armcCmd, "live", file), None, "ARMC", LogNotice)
      } finally {
        SysCmd(Array("rm", file))
      }
    } else {
      Logger.logAndThrow("ARMC", LogError, "cannot create temp file ("+code+"): " + err)
    }

  }
}
