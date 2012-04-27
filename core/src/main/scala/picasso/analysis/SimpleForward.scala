package picasso.analysis

import picasso.math._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import scala.collection.mutable.HashMap
import scala.collection.mutable.HashSet
import scala.collection.Map

trait SimpleForward {
  self : WSTS with WADL =>

  /** Enummerates paths in a BFS way */
  def paths: Iterator[Accelerate[T]] = new Iterator[Accelerate[T]] {
    def hasNext = true

    val prefixes = scala.collection.mutable.Queue[List[T]](Nil)
    var last = transitions.iterator

    def next(): Accelerate[T] = {
      if (last.hasNext) {
        val path = last.next() :: prefixes.head
        prefixes enqueue path
        Accelerate(path.reverse)
      } else {
        prefixes.dequeue
        last = transitions.iterator
        next()
      }
    }
  }
  
  private def traceFromBackTrace(last: Int, map1: Map[Int,(TransfiniteWord[T],Int)], map2: Map[Int,DownwardClosedSet[S]]): TransfiniteTrace[S,T] = map1 get last match {
    case Some((tr, last2)) => traceFromBackTrace(last2, map1, map2).append(map2(last),tr)
    case None => TransfiniteTrace.empty[S,T](map2(last))
  }

  /** Do a search on the words used to build to cover set until it finds the target state. */
  private def mkTrace(init: S, trs: List[TransfiniteWord[T]], target: S): TransfiniteTrace[S,T] = {
    //dropping-keeping transitions one-by-one is exponential so need to be sightly smarter.
    //TODO be smarter latter for the moment build still build a search tree.
    val counter = new java.util.concurrent.atomic.AtomicInteger()
    def getID = counter.incrementAndGet

    val backTrace = new HashMap[Int,(TransfiniteWord[T],Int)]
    val sets = new HashMap[Int,DownwardClosedSet[S]] //put only sets with one basis element
    val cover = new HashSet[Int]

    val initID = getID
    sets += Pair(initID, DownwardClosedSet(init))
    cover += initID

    def explore(trs: List[TransfiniteWord[T]]): Int = trs match {
      case t::ts =>
        val succs = cover.toList map (i => (i, postCover(sets(i),t))) flatMap (p => p._2.basis map ( b => Pair(p._1, DownwardClosedSet(b))))
        val relevant = succs filterNot (p => cover exists (p._2 subsetOf sets(_)))
        relevant foreach (p => cover filterNot (sets(_) subsetOf p._2)) //removes covered elements
        val newIDs = relevant map (p => {
          val id = getID;
          backTrace += Pair(id,(t,p._1));
          sets += Pair(id,p._2); cover += id
          id
        })
        newIDs find (sets(_) contains target) getOrElse explore(ts)
      case Nil => sys.error("SimpleForward.mkTrace: transitions not covering target ?!")
    }

    val covering = if (!(DownwardClosedSet(init) contains target)) explore(trs) else initID
    traceFromBackTrace(covering, backTrace, sets)
  }

  private def transitionsFromBackTrace[A,B](last: A, map: Map[A,(B,A)]): List[B] = map get last match {
    case Some((tr, last2)) => transitionsFromBackTrace(last2, map) ::: List(tr)
    case None => Nil
  }

  private def postAndRecord(states: (Int, DownwardClosedSet[S]),
                            seq: TransfiniteWord[T],
                            record: HashMap[Int,(TransfiniteWord[T],Int)],
                            getID: () => Int
                           ): (Int, DownwardClosedSet[S]) = {
    val after = postCover(states._2, seq)
    if (after subsetOf states._2) {
      states
    } else {
      val id = getID()
      val newStates = states._2 ++ after 
      record += Pair(id, (seq, states._1))
      (id, newStates)
    }
  }

  // enumerates paths and accelerate along those until it converges.
  def forwardCoveringWithTrace(initState: S, targetState: S): Option[TransfiniteTrace[S,T]] = {
    val backTrace = new HashMap[Int,(TransfiniteWord[T],Int)] //version number and transitions
    var counter = -1
    def getID () = {
      counter = counter + 1
      counter
    }
    def myPost(s: (Int, DownwardClosedSet[S]), t: TransfiniteWord[T]) = postAndRecord(s, t, backTrace, getID)
    def oneStep(cover: (Int, DownwardClosedSet[S])) =  (cover /: transitions)( (acc,t) => myPost(acc, Normal(List(t))))

    var accel: List[Accelerate[T]] = Nil
    val acceleration = paths
    var cover = (getID(), DownwardClosedSet(initState))
    var prevID = -1
    
    while (prevID != cover._1 && !cover._2(targetState)) {
      prevID = cover._1
      //TODO this add path one by one, which is way too slow when the number of transition grows.
      //TODO Also there should be some path pruning (partial order reduction)
      accel = acceleration.next :: accel
      val acceld = (cover /: accel)(myPost(_, _))
      cover = oneStep(acceld)
    }
    
    val trace = if (cover._2(targetState)) {
      Logger("Analysis", LogDebug, targetState + " is coverable from " + initState + " : recoverig trace.")
      val transitions = transitionsFromBackTrace(cover._1, backTrace)
      Some(mkTrace(initState, transitions, targetState))
    }else {
      None
    }

    Logger("Analysis", LogDebug,
      trace map (
        targetState + " is coverable from " + initState + " by " + _.toString) getOrElse (
          targetState + " is not coverable from " + initState))
    trace
  }
  
  def forwardCovering(initState: S, targetState: S): Boolean = {
    forwardCoveringWithTrace(initState, targetState).isDefined
  }

  def computeCover(initState: S): DownwardClosedSet[S] = {
    var accel: List[Accelerate[T]] = Nil
    val acceleration = paths
    var cover = DownwardClosedSet(initState)
    var prevCover = DownwardClosedSet.empty[S]
    def oneStep(cover: DownwardClosedSet[S]) =  (cover /: transitions)( (acc,t) => acc ++ postCover(acc, Normal(List(t))))
    while (!(cover subsetOf prevCover)) {
      prevCover = cover
      accel = acceleration.next :: accel
      val acceld = (cover /: accel)( (acc, t) => acc ++ postCover(acc, t))
      cover = oneStep(acceld)
    }
    cover
  }


}
