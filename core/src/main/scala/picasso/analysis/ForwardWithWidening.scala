package picasso.analysis

import picasso.math._
import picasso.graph._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import scala.collection.GenSeq

/** Forward analysis algorightm that uses widening instead of acceleration
TODO:
The simplest approach would be to build a tree/DAG.
how to do it efficiently ?
- keep a list of edges to find the path the was used.
- keep a working list of nodes + their predecessors (flat structure: nodes + set of nodes)
  In order to do widening + subsumption, keep two lists of nodes:
    one list of smallest nodes (for widening)
    one list of biggest nodes (for subsumption)
- algorithm:
  while working not empty
    pick (node, set) in the working list
    for each n \in post(node)
      (1) test whether exists strictly smaller state in set \cup node, if yes widen
      (2a) test if smaller than something already visited: if yes merge the two elements.
      (2b) test if larger than something currently being explored. (WARNING early stop problem)

 */
trait ForwardWithWidening extends CoveringSet {
  self : WSTS with WADL =>

  sealed abstract class Link
  case class TransitionTo(t: T) extends Link
  case class TransitionFrom(t: T) extends Link
  case object WideningTo extends Link
  case object WideningFrom extends Link
  case object Subsumed extends Link
  case object Subsuming extends Link

  type CG /*coverability graph*/ = GT {
    type V = S
    type VL = Unit
    type EL = Link
  }
  
  type TG /*transition graph*/ = GT {
    type V = S
    type VL = Unit
    type EL = T
  }

  type MinElements = UpwardClosedSet[S] //using UpwardClosedSet is a simple trick to easily track the minimal elements

  //TODO better to do the exploration in a DFS/BFS way ?
  //DFS should get faster to some acceleration but not sure about convergence (ascending fork ?)

  def computeEverything(initCover: DownwardClosedSet[S], isDone: S => Boolean): (DownwardClosedSet[S], EdgeLabeledDiGraph[CG], Option[TransfiniteTrace[S,T]]) = {
    var graph = EdgeLabeledDiGraph.empty[CG].addVertices( initCover.basis.seq )
    var cover = initCover
    val workingList = scala.collection.mutable.Stack[(S,MinElements)]()
    for (initState <- initCover.basis.seq) workingList.push(initState -> UpwardClosedSet.empty[S])

    //TODO when adding things to graph: pay attention that two isomorphic graphs are still two different objects.
    //TODO use views for better performance (if successors list becomes too big)

    //filter graph to get only the transitions
    lazy val transitionGraph: EdgeLabeledDiGraph[TG] = {
      val mapWrapped: Map[CG#V,Map[CG#EL, Set[CG#V]]] = graph.adjacencyMap.map{case (n,m) => (n, m.filter{case (TransitionTo(_),_) => true; case _ => false})}
      val mapUnwrapped: Map[TG#V,Map[TG#EL, Set[TG#V]]] = mapWrapped.map{ case (n,m) => (n, m.map{
        case (TransitionTo(t),s) => (t,s)
        case err => Logger.logAndThrow("Analysis", LogError, "expected TransitionTo, not " + err._1)
      })}
      val g = EdgeLabeledDiGraph[TG](mapUnwrapped)
      //println(g.toGraphviz("TG"))
      g
    }

    def getTrace(from: S, to: S): TransfiniteTrace[S,T] = {
      if (from == to) {
        TransfiniteTrace.empty[S,T](DownwardClosedSet(from))
      } else {
        val wideningFrom = graph(to, WideningFrom).toList
        val predecessors = graph.adjacencyMap(to).filterKeys{ case TransitionFrom(_) => true; case _ => false}
        assert(predecessors.size == 1)
        val (pred, trs) = predecessors.iterator.next match {
          case (TransitionFrom(trs), preds) =>
            assert(preds.size == 1)
            (preds.head, trs)
          case err => Logger.logAndThrow("Analysis", LogError, "expected TransitionFrom, not " + err._1)
        }
        //val subsuming = graph(to, Subsuming).toList
        val wideningPaths = wideningFrom map (from2 => Accelerate(transitionGraph.shortestPath(from2, to).labels))
        val prefix = getTrace(from, pred) 
        val nonAccel = postCover(DownwardClosedSet(pred), trs)
        val (last, path) = ((nonAccel -> prefix.append(nonAccel, Normal(List(trs)))) /: wideningPaths)( (acc, word) => {
          val stateAfter = accelerate(acc._1, word.word)
          val pathAfter = acc._2.append(stateAfter, word)
          (stateAfter, pathAfter)
        })
        if (!last(to)) Logger("Analysis", LogWarning, "ForwardWithWidening.getTrace: diverging, the returned trace might be invalid")
        path
      }
    }

    /** Method that checks whether the children of some node can be safely cut.
     *  i.e. the same portion of the state space will be explored from some other place.
     *  The algorithm returns the list of children that can be safely cut.
     *  @param bigger the new nodes that subsumes a node that is currently part of the cover
     *  @param smaller a node (part of the cover basis) that is currently subsumed
     *  @return the list of nodes that can be removed form the cover + workingList
     */
    def nodesToCut(bigger:S): List[S] = {
      //TODO related to this is the example in [Geeraerts, Raskin, and Van Begin, 2007]
      //basic problem: being subsumed by an ancestor of something that one of your ancestor subsumes (subsumption cycle)
      //TODO acually the problem is more complex than that ...
      //cutting children may leads to underapprox and/or non-termination
      //if something is cut yhen we need to be sure that the given part will be explored in another branch.
      //The graph might be huge and subsumption might be quite frequent. Therefore, we should not need to look beyond a few 'path to ancestors'

      //idea (1)
      //  get all the ancestors, also along the Subsuming edges, this is the part which represent a danger of creating cycles
      //  if the node to cut is not in that part => safe to cut, otherwise keepit
      //  #this will probably not work because the last steps in the counter-example involve only new nodes being subsumed
      lazy val dangerZone = sys.error("TODO") //TODO most of the dangerZone is the same for all newOnes -> factor the computation

      //idea (2)
      //  There is also a danger in being subsumed (see cex)
      //  Therefore the whole structure of the algorithm might need to change
      //  What is the underlying invariant/induction hypothesis that is brocken by the counterexample ?
      //    this has probably to do with the 3rd branch cutting the 2nd branch above where the 1st branch was subsumed.
      //  ...

      //TODO test idea on MCT counter-example
      //current algo: yes, does not remove 
      //idea (1): probably not
      //idea (2): ...

      /*
      for ( (_,_,newOne) <- newOnes;
        smaller <- cover.basis.filter(ordering.lt(_,newOne)) ) {
        //TODO add Subsumed/ing edges
        val toCut = canCutChildren(newOne, smaller)
        //TODO remove toCut for the list of thing to process.
        ()
      }
      */
      Nil
    }

    def oneStep(elt: S): GenSeq[(T,S)] = transitions.flatMap( t => post(elt,t).toList.map(s => (t -> s)))

    def widen(elt: S, t: T, s: S, minElts: MinElements): (T, Seq[S], S) = {
      var s2 = s
      def tryWiden(s: S): Boolean = {
        if (ordering.lt(s, s2)) {
          val s3 = widening(s, s2)
          //Logger("Analysis", LogDebug, "ForwardWithWidening, widen:\ns:" + s + "\ns2:" + s2 + "\ns3:" + s3)
          if (ordering.gt(s3,s2)) {
            s2 = s3
            true
          } else false
        } else false
      }
      val usedToWiden = minElts.toList.filter(tryWiden)
      //add new nodes to graph
      val newEdges = (elt, TransitionTo(t), s2) :: (s2, TransitionFrom(t), elt) :: usedToWiden.flatMap(s3 => List((s3,WideningTo,s2),(s2,WideningFrom,s3)))
      graph = graph ++ newEdges
      //return result
      (t, usedToWiden, s2)
    }

    def isSubsumed(s: S): Boolean = {
      if (cover(s)) {
        val by = cover.basis.find(ordering.gteq(_,s)).get
        graph = graph ++ List((s, Subsumed, by), (by, Subsuming, s))
        true
      } else {
        false
      }
    }

    //print the size of the cover periodically
    var time = java.lang.System.currentTimeMillis
    def logIteration {
      val newTime = java.lang.System.currentTimeMillis
      if (newTime - time > 10000) {
        Logger("Analysis", LogInfo, "ForwardWithWidening: cover has size " + cover.size)
        Logger("Analysis", LogDebug, "ForwardWithWidening: cover is " + cover)
        time = newTime
      }
    }

    def process: Option[TransfiniteTrace[S,T]] = workingList.headOption match {
      case Some((elt, minElts)) =>
        workingList.pop
        val successors = oneStep(elt)
        val widened = successors.map { case (t,s) => widen(elt, t, s, minElts) }
        val (subsumed, newOnes) = widened partition { case (_,_,s) => isSubsumed(s) }
        //TODO subsuming: if we cut childrens, we remove parts of the cover: this is the tricky part for termination and soundness see nodesToCut
        //however this is likely to be critical for performance ...
        //newOnes
        for ((_, _, s) <- newOnes) {
          workingList push (s -> (minElts + elt))
          //if (!cover(s)) Logger("Analysis", LogInfo, "new element in cover: " + s)
          cover = cover + s
        }
        logIteration
        //if post generates something that covers the targetState then trace else recurse
        val covering = newOnes find { case (_,_,s) => isDone(s)}
        val trace: Option[TransfiniteTrace[S,T]] = covering flatMap { case (_,_,s) =>
            initCover.view.map(initState => try Some(getTrace(initState, s)) catch { case _ => None }).find(_.isDefined).get
        }
        if (trace.isDefined) trace else process
      case None => None
    }

    //filter trivial case where the init state cover the targetState
    val trace =
      if (initCover.exists(initState => isDone(initState))) Some(TransfiniteTrace.empty[S,T](cover))
      else process
    (cover, graph, trace)
  }

  def computeCover(initCover: DownwardClosedSet[S]) = {
    val (cover, _, _) = computeEverything(initCover, ((_:S) => false))
    cover
  }
  
  def forwardCoveringWithTrace(initState: S, targetState: S): Option[TransfiniteTrace[S,T]] = {
    val (_, _, trace) = computeEverything(DownwardClosedSet(initState), ordering.gteq(_, targetState))
    trace
  }

  def forwardCovering(initState: S, targetState: S): Boolean = {
    forwardCoveringWithTrace(initState, targetState).isDefined
  }

}
