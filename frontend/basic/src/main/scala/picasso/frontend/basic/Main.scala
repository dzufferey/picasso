package picasso.frontend.basic

import picasso.utils._
import picasso.frontend.basic.typer._

object Main {

  //TODO adapt to the new report + runner infrastructure.
  //the problem is the Analysis/DBPWrapper/DefDBP -> dig out the type if DBP

  def main(args: Array[String]) {
    Config(args.toList) //process the cmdline args
    val report = Config.input match {
      case fn :: _ => analyse(fn, IO.readTextFile(fn))
      case Nil => analyse("stdin", IO.readStdin)
    }
    report.makeConsoleReport
    val woDir = (new java.io.File(args(0))).getName()
    val woSuffix = {
      val lastDot = woDir.lastIndexOf('.')
      if (lastDot > 0) woDir.substring(0, lastDot)
      else woDir
    }
    report.makeHtmlReport(woSuffix + "-report.html")
  }

  def analyse(fn: String, content: String) = {
    val report = new Report(fn)
    val pr = BasicParser(content)
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
