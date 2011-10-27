package picasso.frontend.basic

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.basic.typer._

object Main {

  def main(args: Array[String]) {
    //TODO put all the pieces toghether: up to Analysis
    //TODO a simple typer: to know what tings are references and declarations (env to help the conversion)
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
        new Analysis(agents, initAst)
      } else {
        Logger.logAndThrow("basic", LogError, "cannot type "+fn+":\n"+typedActors)
      }
    } else {
      Logger.logAndThrow("basic", LogError, "cannot parse "+fn+":\n"+pr)
    }
  }

}
