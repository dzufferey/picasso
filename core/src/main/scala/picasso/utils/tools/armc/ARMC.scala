package picasso.utils.tools.armc

import picasso.model.integer._
import picasso.utils._

object ARMC {

  protected def exec[A](prog: Program, execFct: String => A): A = {
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      try {
        val armcProg = prog.printForARMC
        Logger("ARMC", LogInfo, "program:\n" + armcProg)
        IO.writeInFile(file, armcProg)
        execFct(file)
      } finally {
        SysCmd(Array("rm", file))
      }
    } else {
      Logger.logAndThrow("ARMC", LogError, "cannot create temp file ("+code+"): " + err)
    }
  }

  def withOutput(prog: Program) = {
    exec(prog, file => SysCmd.execOutputAndLog(Array(Config.armcCmd, "live", file), None, "ARMC", LogNotice))
  }

  def apply(prog: Program) {
    exec(prog, file => SysCmd.execRedirectToLogger(Array(Config.armcCmd, "live", file), None, "ARMC", LogNotice))
  }
}
