package picasso.analysis

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer}
import picasso.model.dbp._
import picasso.graph._
import picasso.math.DownwardClosedSet
import picasso.model.integer._
import scala.collection.parallel.{ParIterable, ParSeq}

trait DBPTermination2[P <: DBCT] extends DBPTerminationCommon[P] {
  self: DepthBoundedProcess[P] =>

  //rather than build the program using the full tree, use only the cover
  //from the cover -> take the one step successors -> find out the back edges for each sucessors
  //initialisation: to any element of the cover with "any" counter value


  protected def oneStepPostWithWitness(current: S): ParIterable[TransitionWitness[P]] = {
    val possible = transitions.filter(_ isDefinedAt current).par
    for( t <- possible;
         (w,_) <- t.applyWithWitness( current ) ) yield {
        w
    }
  }

  protected def makeEdges(states: ParIterable[S]): ParIterable[(S, TransitionWitness[P], S)] = {
    for ( s1 <- states;
          w <- oneStepPostWithWitness(s1);
          s2 <- states if ordering.lteq(w.to, s2)
        ) yield (s1, w, s2)
  }

  protected def makeTransitions(edges: ParIterable[(S, TransitionWitness[P], S)]): ParIterable[Transition] = {
    edges.flatMap{ case (a, w, b) =>
      simplifyPath( transitionForWitness1(w) ) ++ covering(w.to, b) //todo if only one covering edges -> we can add the edge as part of the path to simplify
    }
  }

  def makeIntegerProgram(cover: DownwardClosedSet[S]): Program = {
    val edges = makeEdges(cover.basis)
    val trs = makeTransitions(edges)
    val variables = (Set[Variable]() /: trs)(_ ++ _.variables)
    val initials = for (init <- cover.basis.toSeq.par) yield initialize(init, variables)
    val initState = initials.head.sourcePC
    //TODO
    new Program(initState, (initials ++ trs): ParSeq[Transition] )
  }

  def termination(initState: S) = {
    val (cover, tree) = computeTree(initState)
    Logger("DBPTermination", LogNotice, "Extracting numerical abstraction from the cover.")
    val program1 = makeIntegerProgram(cover)
    Logger("DBPTermination", LogNotice, "Extraction done. Simplifying ... ")
    val program2 = program1.simplifyForTermination
    Logger("DBPTermination", LogNotice, "Removing sinks")
    val program3 = ProgramHeuritics.removeSinks(program2)
    (cover, tree, program3)
  }
}
