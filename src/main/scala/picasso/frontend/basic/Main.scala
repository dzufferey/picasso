package picasso.frontend.basic

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.basic.typer._

object Main {

  def main(args: Array[String]) {
    val a = mkAnalysis(args(0))
    val c = a.computeCover
    Console.println("Cover is:\n" + c)
  }

  def mkAnalysis(fn: String) = {
    val pr = BasicParser.parseFile(fn)
    if (pr.successful) {
      val (actors, init) = pr.get
      Logger("basic", LogDebug, "Parsed:\n" + actors.mkString("","\n\n",""))
      val typedActors = Typer(actors)
      if (typedActors.success) {
        val tActors = typedActors.get
        Logger("basic", LogNotice, "Input Program:\n\n" + tActors.mkString("","\n\n","") + "\n")
        val agents = tActors map Actors.actor2Agent
        Logger("basic", LogNotice, "As CFA:\n\n" + agents.mkString("","\n\n","") + "\n")
        val initAst = Expressions.exp2Exp(init)
        //TODO type initAst
        new Analysis(agents, initAst)
      } else {
        Logger.logAndThrow("basic", LogError, "cannot type "+fn+":\n"+typedActors)
      }
    } else {
      Logger.logAndThrow("basic", LogError, "cannot parse "+fn+":\n"+pr)
    }
  }

}
