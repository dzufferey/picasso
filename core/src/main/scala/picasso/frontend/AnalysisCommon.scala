package picasso.frontend

import picasso.utils._
import picasso.utils.report._
import picasso.model.dbp._
import picasso.analysis.KarpMillerTree

abstract class AnalysisCommon[P <: picasso.model.dbp.DBCT](
    what: String,
    fileName: String,
    content: String,
    parse: String => Option[(DepthBoundedProcess[P], DepthBoundedConf[P], Option[DepthBoundedConf[P]])])
{

  protected var done = false
  protected val report = new Report("Computing "+what+" of " + fileName)

  protected def addProcessToReport(process: DepthBoundedProcess[P], init: DepthBoundedConf[P]) {
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

  protected def analysis(process: DepthBoundedProcess[P], init: DepthBoundedConf[P], target: Option[DepthBoundedConf[P]]): Unit

  def analyse: Report = {
    if (done) {
      report
    } else {
      Report.set(report)
      report.add(new PreformattedText("Input", content))

      parse(content) match {
        case Some((process, init, target)) =>
     
          Logger("dbpGraph", LogInfo, process.toString) 
          addProcessToReport(process, init)

          analysis(process, init, target)

          if (Config.stats) {
            report.add(Stats.report)
            Logger("dbpGraph", LogNotice, Stats.toString) 
          }
     
          if (Config.report) {
            val woDir = (new java.io.File(fileName)).getName()
            val woSuffix = {
              val lastDot = woDir.lastIndexOf('.')
              if (lastDot > 0) woDir.substring(0, lastDot)
              else woDir
            }
            report.makeHtmlReport(woSuffix + "-report.html")
          }

          Report.reset
          report
     
        case None =>
          Logger.logAndThrow("dbpGraph", LogError, "parsing of '" + fileName + "' failed")
      }
    }
  }

}
