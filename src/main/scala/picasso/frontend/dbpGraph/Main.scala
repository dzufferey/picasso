package picasso.frontend.dbpGraph

import picasso.utils._
import picasso.model.dbp._

object Main {

  def main(args: Array[String]) {
    Args(args.toList) //process the cmdline args
    Args.input match {
      case Some(fn) => analyse(fn, IO.readTextFile(fn))
      case None => analyse("stdin", IO.readStdin)
    }
  }

  def analyse(fn: String, content: String) = {
    DBPGraphParser(content) match {
      case Some((init, trs, traget)) =>
        val process = new DepthBoundedProcess(trs)
        Logger("dbpGraph", LogInfo, Misc.docToString(process.toGraphviz("DBPGraph")) )
        val coverKM = DBPGraphs.computeCoverKM(init, trs)
        Logger("dbpGraph", LogNotice, "cover:\n" + coverKM)
      case None =>
        Logger.logAndThrow("dbpGraph", LogError, "parsing of '" + fn + "' failed")
    }
  }

}
