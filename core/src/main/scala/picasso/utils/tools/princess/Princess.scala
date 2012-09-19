package picasso.utils.tools.princess

import picasso.math.hol._
import picasso.utils._

object Princess {

  def eliminateQuantifiers(universalConstants: Set[Variable], existentialConstants: Set[Variable], f: Formula): Option[Formula] = {
    val toVar = scala.collection.mutable.HashMap[String, Variable]()
    val (code, file, err) = SysCmd(Array("mktemp"))
    if (code == 0) {
      val (success, stdout, stderr) =
        try {
          Logger("princess", LogInfo, "query:")
          Logger("princess", LogInfo, Printer(_, universalConstants, existentialConstants, f))
          IO.writeInFile(file, Printer(_, universalConstants, existentialConstants, f))
          SysCmd(Array(Config.princessCmd, "+mostGeneralConstraint", file))
        } finally {
          SysCmd(Array("rm", file))
        }
      if (success == 0) {
        //parse the result
        //TODO identify whether it succeeded or not
        //TODO get the formula and parse it
        sys.error("TODO")
      } else {
        Logger.logAndThrow("ARMC", LogError, "princess failed ("+success+"): " + stderr)
        None
      }
    } else {
      Logger.logAndThrow("ARMC", LogError, "cannot create temp file ("+code+"): " + err)
      None
    }
  }

  
}
