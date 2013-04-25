package picasso.utils.tools.flata

import picasso.utils.tools.nts.NTSPrinter
import picasso.model.integer._
import picasso.utils._

object Flata {

  protected def exec[A](prog: Program, execFct: String => A): A = {
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      try {
        val nts = NTSPrinter.asString(prog)
        Logger("Flata", LogInfo, "program:\n" + nts)
        //SysCmd.execRedirectToLogger(Array("echo", file), None, "asdf", LogError)
        //SysCmd.execRedirectToLogger(Array("cat", file), None, "asdf", LogError)
        IO.writeInFile(file.trim, nts)
        //SysCmd.execRedirectToLogger(Array("cat", file), None, "asdf", LogError)
        execFct(file.trim)
      } finally {
        SysCmd(Array("rm", file))
      }
    } else {
      Logger.logAndThrow("Flata", LogError, "cannot create temp file ("+code+"): " + err)
    }
  }

  def withOutput(prog: Program) = {
    exec(prog, file => SysCmd.execOutputAndLog(Array(Config.flataCmd, file), None, "Flata", LogNotice))
  }

  def apply(prog: Program) {
    exec(prog, file => SysCmd.execRedirectToLogger(Array(Config.flataCmd, file), None, "Flata", LogNotice))
  }
}
