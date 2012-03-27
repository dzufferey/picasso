package picasso.frontend.dbpGraph

import picasso.utils._
import picasso.utils.report._
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

  private def addProcessToReport[P <: picasso.model.dbp.DBCT](report: Report, process: DepthBoundedProcess[P], init: DepthBoundedConf[P]) {
    val initial = new GenericItem(
                    "Initial Configuration",
                    init.toGraphviz("Init"),
                    Misc.graphvizToSvgFdp(init.toGraphviz("init"))
                  )
    val trs = new List("Transitions")
    for (t <- process.transitions.seq) {
      trs.add( new GenericItem(
        t.id,
        Misc.docToString(t.toGraphviz("trs")),
        Misc.graphvizToSvgDot(Misc.docToString(t.toGraphviz("trs")))
      ))
    }
    val lst = new List("Graph rewriting system")
    lst.add(initial)
    lst.add(trs)
    report.add(lst)
  }
  
  def analyse(fn: String, content: String) = {
    DBPGraphParser(content) match {
      case Some((init, trs, traget)) =>
        val report = new Report("Analysis of " + fn)
        report.add(new PreformattedText("Input", content))

        val process = new DepthBoundedProcess(trs) with KarpMillerTree
        Logger("dbpGraph", LogInfo, Misc.docToString(process.toGraphviz("DBPGraph")) )
        addProcessToReport(report, process, init)

        val (cover, tree) = process.computeTree(init)

        if (Config.KM_showTree) {
          val treeAsGV = process.TreePrinter.printGraphviz(tree , (t, id, pref) => t().toGraphvizFull(id, "subgraph", "", pref)._1 )
          Logger("dbpGraph", LogInfo, "tree:\n" + treeAsGV )
          report.add( new GenericItem( "KM Tree", treeAsGV,Misc.graphvizToSvgFdp(treeAsGV) ))
        }

        Logger("dbpGraph", LogNotice, "cover:\n" + cover)
        val coverReport = new List("Cover")
        for ((c, i) <- cover.zipWithIndex) {
          coverReport.add( new GenericItem(
            "cover element " + i,
            c.toGraphviz("cover"),
            Misc.graphvizToSvgFdp(c.toGraphviz("cover"))
          ))
        }
        report.add(coverReport)

        if (Config.report) {
          val woDir = (new java.io.File(fn)).getName()
          val woSuffix = {
            val lastDot = woDir.lastIndexOf('.')
            if (lastDot > 0) woDir.substring(0, lastDot)
            else woDir
          }
          report.makeHtmlReport(woSuffix + "-report.html")
        }

      case None =>
        Logger.logAndThrow("dbpGraph", LogError, "parsing of '" + fn + "' failed")
    }
  }

}
