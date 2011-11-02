package picasso.frontend.basic

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.basic.typer._

object Main {

  def main(args: Array[String]) {
    val r = analyse(args(0))
    r.makeConsoleReport
  }

  def analyse(fn: String) = {
    val report = new Report(fn)
    val pr = BasicParser.parseFile(fn)
    if (pr.successful) {
      val (actors, init) = pr.get
      report.setParsed((actors, init))
      Logger("basic", LogDebug, "Parsed:\n" + actors.mkString("","\n\n",""))
      val typedActors = Typer(actors)
      if (typedActors.success) {
        val tActors = typedActors.get
        report.setTyped(tActors)
        Logger("basic", LogNotice, "Input Program:\n\n" + tActors.mkString("","\n\n","") + "\n")
        val agents = tActors map Actors.actor2Agent
        report.setAgents(agents)
        Logger("basic", LogNotice, "As CFA:\n\n" + agents.mkString("","\n\n","") + "\n")
        val initAst = Expressions.exp2Exp(init)
        //TODO type initAst
        val a = new Analysis(agents, initAst)
        report.setTransitions(a.transitions)
        report.setInitConf(a.initConf)
        val c = a.computeCover
        report.setCover(c)
      } else {
        report.setError("cannot type:\n"+typedActors)
        Logger.logAndThrow("basic", LogError, "cannot type "+fn+":\n"+typedActors)
      }
    } else {
      report.setError("cannot parse:\n"+pr)
      Logger.logAndThrow("basic", LogError, "cannot parse "+fn+":\n"+pr)
    }
    report
  }

}
