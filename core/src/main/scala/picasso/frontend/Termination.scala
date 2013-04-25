package picasso.frontend

import picasso.utils._
import picasso.utils.report._
import picasso.utils.tools.armc._
import picasso.utils.tools.flata._
import picasso.utils.tools.nts._
import picasso.model.dbp._
import picasso.model.integer._
import picasso.analysis._

class Termination[P <: picasso.model.dbp.DBCT](
    fileName: String,
    content: String,
    parse: String => Option[(DepthBoundedProcess[P], DepthBoundedConf[P], Option[DepthBoundedConf[P]])]
  ) extends AnalysisCommon[P]("Termination", fileName, content, parse)
{

  protected def dump(file: String, prog: Program) {
    Logger("Termination", LogInfo, "saving integer program in " + file)
    if (Config.flata) {
      IO.writeInFile(file, NTSPrinter(_, prog))
    } else {
      IO.writeInFile(file, prog.printForARMC(_))
    }
  }

  protected def analyse(prog: Program) = {
    if (Config.flata) {
      Stats("proving termination with Flata", Flata.withOutput(prog))
    } else {
      Stats("proving termination with ARMC", ARMC.withOutput(prog))
    }
  }

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

    if (Config.dumpIntProg == "") {
      val (_, out, _) = analyse(intProgram)
      report.add(new PreformattedText("Termination analysis", out))
    } else {
      dump(Config.dumpIntProg, intProgram)
    }
  }

}
