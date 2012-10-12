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

    val process = new DepthBoundedProcess( _process) with KarpMillerTree with DBPTermination[P]
    val (cover, tree) = Stats("cover computation", process.computeTree(init))
     
    val coverReport = new List("Cover")
    for ((c, i) <- cover.zipWithIndex) {
      coverReport.add( new GenericItem(
        "cover element " + i,
        c.toGraphviz("cover"),
        Misc.graphvizToSvgFdp(c.toGraphviz("cover"))
      ))
    }
    report.add(coverReport)

    val intProgram = Stats("extracting numerical abstraction", process.termination(cover))
    Stats.comment("numerical abstraction has " +
                  intProgram.pcs.size + " locations, " +
                  intProgram.variables.size + " variables, " +
                  intProgram.transitions.size + " transitions.")
    report.add(new PreformattedText("Numerical Abstraction", intProgram.printForARMC))

    if (Config.dumpArmc == "") {
      val (code, out, err) = Stats("proving termination with ARMC", ARMC.withOutput(intProgram))
      report.add(new PreformattedText("ARMC output", out))
    } else {
      Logger("Termination", LogInfo, "saving ARMC program in " + Config.dumpArmc)
      IO.writeInFile(Config.dumpArmc, intProgram.printForARMC(_))
    }
  }

}
