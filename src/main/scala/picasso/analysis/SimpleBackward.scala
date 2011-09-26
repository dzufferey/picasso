package picasso.analysis

import picasso.graph.Trace
import picasso.math._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import scala.collection.mutable.HashMap
import scala.collection.Map

trait SimpleBackward {
  self : WSTS with PredBasis =>
  

  private def transitionFromBackTrace[A](last: A, map: Map[A,(T,A)]): List[T] = map get last match {
    case Some((tr, last2)) => tr :: transitionFromBackTrace(last2, map)
    case None => Nil
  }

  private def findCovering(start: S, transitions: List[T], target: S): Option[Trace[S,T]] = transitions match {
    case t :: ts =>
      ((None: Option[Trace[S,T]]) /: post(start, t))( (acc, s) => acc orElse (findCovering(s, ts, target) map (_.prepend(start, t)))) 
    case Nil =>
      if (ordering.gteq(start, target)) Some(Trace(start))
      else None
  }

  def preAndLog(pre: UpwardClosedSet[S], all: UpwardClosedSet[S], backTrace: HashMap[S,(T,S)]): UpwardClosedSet[S] = {
    val indep = pre.basis.toList
    val withPre = indep map (s => (s, transitions map ( t => (t, predBasis(UpwardClosedSet(s),t)))))
    val withPreFlat = withPre flatMap { case (s, lst) => lst map { case (t, p) => (s, t, p) }}
    val relevant = withPreFlat flatMap { case (s, t, pre) =>
      val newOnes = pre.basis filterNot (all contains _)
      newOnes map ((s,t,_))
    }
    relevant foreach { case (s, t, p) => backTrace += Pair(p, Pair(t,s)) }
    (UpwardClosedSet.empty[S] /: relevant)(_ + _._3)
  }
  
  def backwardCoveringWithTrace(initState: S, targetState: S): Option[Trace[S,T]] = {
    val backTrace = new HashMap[S,(T,S)] //a state to its prececessors.
    def lazySaturate(states: UpwardClosedSet[S], last: UpwardClosedSet[S]): Option[S] = {
      if (states contains initState) {
        //stops when found: do not saturate to the end.
        states elementCovering initState
      } else {
        val newOnes = preAndLog(last, states, backTrace)
        val states2 = states ++ newOnes
        if (states == states2) None
        else lazySaturate(states2, newOnes)
      }
    }
    val init = UpwardClosedSet[S](scala.collection.immutable.Set(targetState))
    val last = lazySaturate(init, init)
    Logger("Analysis", LogDebug,
      last map (targetState + " is covered from " + _ + " which is below " + initState)
      getOrElse(targetState + " is not coverable from " + initState))
    val path = last map (transitionFromBackTrace(_, backTrace))
    Logger("Analysis", LogDebug, path map ("Path is " + _.mkString("(",";",")")) getOrElse("Path not found"))
    val trace = path flatMap (findCovering(initState, _, targetState))
    Logger("Analysis", LogDebug, trace map (_.toString) getOrElse("No trace"))
    trace
  }


  def backwardCovering(initState: S, targetState: S): Boolean = {
    //blindly compute the pre until it does not change.
    def saturate(states: UpwardClosedSet[S]): UpwardClosedSet[S] = {
      val states2 = states ++ predBasis(states)
      if (states == states2) states else saturate(states2)
    }
    val coverableFrom = saturate(UpwardClosedSet(scala.collection.immutable.Set(targetState)))
    Logger("Analysis", LogDebug, targetState + " is coverable from " + coverableFrom)
    coverableFrom(initState)
  }

}
