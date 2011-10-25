package picasso.frontend.basic

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

object Main {

  def main(args: Array[String]) {
    //TODO put all the pieces toghether: up to Analysis
    //TODO a simple typer: to know what tings are references and declarations (env to help the conversion)
  }

  def mkAnalysis(fn: String) = {
    val pr = BasicParser.parseFile(fn)
    if (pr.successful) {
      val (actors, init) = pr.get
      def agents = actors map Actors.actor2Agent
      val initAst = Expressions.exp2Exp(init)
      new Analysis(agents, initAst)
    } else {
      Logger.logAndThrow("basic", LogError, "cannot parse "+fn+":\n"+pr)
    }
  }

}
