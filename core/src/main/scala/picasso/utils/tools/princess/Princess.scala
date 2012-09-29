package picasso.utils.tools.princess

import picasso.math.hol._
import picasso.utils._

object Princess {

  protected def processOutput(out: String, err: String): Option[Formula] = {
    val toLookFor = "Formula is valid, resulting most-general constraint:"
    val lines = out.lines.dropWhile(l => !l.startsWith (toLookFor))
    if (lines.hasNext) {
      lines.next
      val formulaStr = lines.next
      Parser.parseExpression(formulaStr)
    } else {
      Logger("princess", LogWarning, "princess could not solve ?:\n" + out + "\n" + err)
      None
    }
  }

  def eliminateQuantifiersFile(file: String): Option[Formula] = {
    val (success, stdout, stderr) = SysCmd(Array(Config.princessCmd, "+mostGeneralConstraint", "-inputFormat=pri", "-logo", file))
    if (success == 0) {
      processOutput(stdout, stderr)
    } else {
      Logger.logAndThrow("princess", LogError, "princess failed ("+success+"):\n" + stderr)
      None
    }
  }

  def eliminateQuantifiers(universalConstants: Set[Variable], existentialConstants: Set[Variable], f: Formula): Option[Formula] = {
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      try {
        Logger("princess", LogInfo, "query:")
        Logger("princess", LogInfo, Printer(_, universalConstants, existentialConstants, f))
        IO.writeInFile(file, Printer(_, universalConstants, existentialConstants, f))
        eliminateQuantifiersFile(file).map(f => {
          val varsLeft = universalConstants ++ existentialConstants
          val toVar = (Map[Variable, Variable]() /: (varsLeft))( (acc, v) => acc + (Variable(Printer.asVar(v)) -> v))
          f.alpha(toVar)
        })
      } finally {
        SysCmd(Array("rm", file))
      }
    } else {
      Logger.logAndThrow("princess", LogError, "cannot create temp file ("+code+"): " + err)
      None
    }
  }
  
  def isValidFile(file: String): Option[Boolean] = {
    val (success, stdout, stderr) = SysCmd(Array(Config.princessCmd, "-inputFormat=pri", "-logo", file))
    if (success == 0) {
      val toLookFor1 = "Formula is valid"
      val toLookFor2 = "Formula is invalid"
      if (stdout contains toLookFor1) {
        Logger("princess", LogDebug, "princess says valid.")
        Some(true)
      } else if (stdout contains toLookFor2) {
        Logger("princess", LogDebug, "princess says invalid.")
        Some(false)
      } else {
        Logger("princess", LogDebug, "princess says ? -> " + stdout)
        None
      }
    } else {
      Logger.logAndThrow("princess", LogError, "princess failed ("+success+"):\n" + stderr)
      None
    }
  }

  def isValid(universalConstants: Set[Variable], existentialConstants: Set[Variable], f: Formula): Option[Boolean] = {
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      try {
        Logger("princess", LogInfo, "query:")
        Logger("princess", LogInfo, Printer(_, universalConstants, existentialConstants, f))
        IO.writeInFile(file, Printer(_, universalConstants, existentialConstants, f))
        isValidFile(file)
      } finally {
        SysCmd(Array("rm", file))
      }
    } else {
      Logger.logAndThrow("princess", LogError, "cannot create temp file ("+code+"): " + err)
      None
    }
  }
  
}
