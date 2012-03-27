package picasso.analysis

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.model.dbp._

trait DBPTermination[P <: DBCT] extends KarpMillerTree {
  self: DepthBoundedProcess[P] =>

  //(1) compute the cover and extract the transition witnesses
  //(2) build some sensible datastructure out of the witnesses buffers
  //(3) using the witnesses create an integer program ...

  val transitionWitnesses = new java.util.concurrent.ConcurrentLinkedQueue[TransitionWitness[P]]()
  val wideningWitnesses = new java.util.concurrent.ConcurrentLinkedQueue[WideningWitnessSeq[P]]()

  //override oneStepPost to get the transition witnesses
  override protected def oneStepPost(current: KMTree): scala.collection.GenSeq[(T, S)] = {
    val possible = transitions.filter(_ isDefinedAt current()).par
    for( t <- possible;
         (w,s) <- t.applyWithWitness( current() ) ) yield {
        transitionWitnesses.add(w)
        (t,s)
    }
  }

  //override wideningPolicy to get the widening witnesses
  override protected def wideningPolicy(current: KMTree, t: T, s: S): KMNode = {
    val acceleratedFrom = current.ancestorSmaller(s)
    val reducedSeq = expBackoff(acceleratedFrom)
    /*
    val s2 = (s /: reducedSeq)( (bigger, smaller) => widening(smaller(), bigger))
    KMNode(current, t, s2, acceleratedFrom.toList)
    */
    sys.error("TODO")
  }

}
