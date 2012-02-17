package picasso.frontend.dbpGraph

import picasso.utils._
import picasso.model.dbp._
import picasso.analysis.KarpMillerTree

object Main {

  def main(args: Array[String]) {
    Config(args.toList) //process the cmdline args
    Config.input match {
      case fn :: _ => analyse(fn, IO.readTextFile(fn))
      case Nil => analyse("stdin", IO.readStdin)
    }
  }

  def analyse(fn: String, content: String) = {
    DBPGraphParser(content) match {
      case Some((init, trs, traget)) =>
        val process = new DepthBoundedProcess(trs) with KarpMillerTree
        Logger("dbpGraph", LogInfo, Misc.docToString(process.toGraphviz("DBPGraph")) )
        val (cover, tree) = process.computeTree(init)
        Logger("dbpGraph", LogInfo, "tree:\n" +
          process.TreePrinter.printGraphviz(tree , (t, id, pref) => t().toGraphvizFull(id, "subgraph", "", pref)._1 ))
        Logger("dbpGraph", LogNotice, "cover:\n" + cover)
      case None =>
        Logger.logAndThrow("dbpGraph", LogError, "parsing of '" + fn + "' failed")
    }
  }

}
