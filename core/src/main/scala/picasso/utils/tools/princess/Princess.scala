package picasso.utils.tools.princess

import picasso.math.hol._
import picasso.utils._

object Princess {

  protected def processOutput(out: String): Option[Formula] = {
    val toLookFor = "Formula is valid, resulting most-general constraint:"
    val lines = out.lines.dropWhile(l => !l.startsWith (toLookFor))
    if (lines.hasNext) {
      val formulaStr = lines.next.substring(toLookFor.length)
      Parser.parseExpression(formulaStr)
    } else {
      Logger("princess", LogWarning, "princess could not solve ?: " + out)
      None
    }
  }

  def eliminateQuantifiersFile(file: String): Option[Formula] = {
    val (success, stdout, stderr) = SysCmd(Array(Config.princessCmd, "+mostGeneralConstraint", "-inputFormat=pri", file))
    if (success == 0) {
      processOutput(stdout)
    } else {
      Logger.logAndThrow("princess", LogError, "princess failed ("+success+"): " + stderr)
      None
    }
  }

  def eliminateQuantifiers(universalConstants: Set[Variable], existentialConstants: Set[Variable], f: Formula): Option[Formula] = {
    val toVar = scala.collection.mutable.HashMap[String, Variable]()
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      try {
        Logger("princess", LogInfo, "query:")
        Logger("princess", LogInfo, Printer(_, universalConstants, existentialConstants, f))
        IO.writeInFile(file, Printer(_, universalConstants, existentialConstants, f))
        eliminateQuantifiersFile(file)
      } finally {
        SysCmd(Array("rm", file))
      }
    } else {
      Logger.logAndThrow("princess", LogError, "cannot create temp file ("+code+"): " + err)
      None
    }
  }
  
}
