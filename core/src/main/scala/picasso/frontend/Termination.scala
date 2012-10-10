package picasso.frontend

import picasso.utils._
import picasso.utils.report._
import picasso.utils.tools.armc._
import picasso.model.dbp._
import picasso.model.integer.Program
import picasso.analysis._

class Termination[P <: picasso.model.dbp.DBCT](
    fileName: String,
    content: String,
    parse: String => Option[(DepthBoundedProcess[P], DepthBoundedConf[P], Option[DepthBoundedConf[P]])]
  ) extends AnalysisCommon[P]("Termination", fileName, content, parse)
{

  protected def analysis(_process: DepthBoundedProcess[P], init: DepthBoundedConf[P], target: Option[DepthBoundedConf[P]]): Unit = {
    assert(target.isEmpty, "Termination analysis does not expect a target state")

    val process = new DepthBoundedProcess( _process) with DBPTermination[P]
    val (cover, tree, intProgram) = process.termination(init)
     
    val coverReport = new List("Cover")
    for ((c, i) <- cover.zipWithIndex) {
      coverReport.add( new GenericItem(
        "cover element " + i,
        c.toGraphviz("cover"),
        Misc.graphvizToSvgFdp(c.toGraphviz("cover"))
      ))
    }
    report.add(coverReport)

    report.add(new PreformattedText("Numerical Abstraction", intProgram.printForARMC))

    if (Config.dumpArmc == "") {
      //TODO save ARMC output in the report ??
      ARMC(intProgram)
    } else {
      Logger("Termination", LogInfo, "saving ARMC program in " + Config.dumpArmc)
      IO.writeInFile(Config.dumpArmc, intProgram.printForARMC(_))
    }
  }

}
