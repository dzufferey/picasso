package picasso.frontend.basic

import picasso.utils._
import picasso.utils.report._
import picasso.ast._
import picasso.model.dbp._
import picasso.frontend.basic.typer._
import picasso.frontend._

object Main extends Runner[DBC] {

  protected def reportTyped(acts: Iterable[Actor]) {
    Logger("basic", LogNotice, "Input Program:\n\n" + acts.mkString("","\n\n","") + "\n")
    val lst = new List("Typed Actors:")
    Report add lst
    for ( a <- acts ) lst.add(new PreformattedText(a.id, a.toString))
  }

  protected def reportAgents(agents: Iterable[AgentDefinition[Actors.PC]]) {
    Logger("basic", LogNotice, "As CFA:\n\n" + agents.mkString("","\n\n","") + "\n")
    val lst = new List("Actor's CFAs:")
    Report add lst
    for ( a <- agents ) {
      lst.add(new GenericItem(a.id + a.params.mkString("(",", ",")"),
                              a.toString,
                              Misc.graphvizToSvgDot(Misc.docToString(a.toGraphviz("agent", "digraph", "agt")))))
    }
  }

  def parse(input: String): Option[(DepthBoundedProcess[DBC], DepthBoundedConf[DBC], Option[DepthBoundedConf[DBC]])] = {
    val pr = BasicParser(input)
    if (pr.successful) {
      val (actors, init) = pr.get
      val typedActors = Typer(actors)
      if (typedActors.success) {
        val tActors = typedActors.get //Iterable[Actor]
        reportTyped(tActors)
        val agents = tActors map Actors.actor2Agent //Iterable[AgentDefinition[Actors.PC]]
        reportAgents(agents)
        val initAst = Expressions.exp2Exp(init)
        //TODO type initAst
        val a = new Analysis(agents, initAst)
        Some((a.system, a.initConf, None))
      } else {
        Report.add( new PreformattedText("Typing Error", typedActors.toString))
        None
      }
    } else {
      Report.add( new PreformattedText("Parsing Error", pr.toString))
      None
    }
  }


}
