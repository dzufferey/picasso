package picasso.analysis

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer}
import picasso.model.dbp._
import picasso.graph._

trait DBPTermination[P <: DBCT] extends DBPTerminationCommon[P] {
  self: DepthBoundedProcess[P] =>

  //(1) compute the cover and extract the transition witnesses
  //(2) build some sensible datastructure out of the witnesses buffers
  //(3) using the witnesses create an integer program ...
  //(4) methods to compute KM + test integer program

  protected val transitionWitnesses = new java.util.concurrent.ConcurrentLinkedQueue[TransitionWitness[P]]()
  protected val wideningWitnesses = new java.util.concurrent.ConcurrentLinkedQueue[WideningWitnessSeq[P]]()

  //(1)

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
    var witnesses: List[WideningWitness[P]] = Nil
    val s2 = (s /: reducedSeq)( (bigger, smaller) => {
      val (bigger2, witness) = wideningWithWitness(smaller(), bigger)
      witnesses = witness :: witnesses
      bigger2
    })
    val seqWitness = new WideningWitnessSeq[P]
    seqWitness.from = s
    seqWitness.to = s2
    seqWitness.sequence = witnesses.reverse
    wideningWitnesses.add(seqWitness)
    KMNode(current, t, s2, acceleratedFrom.toList)
  }

  //(2)
  //to connect the wideningWitnesses with the transitionWitnesses ...
  //in the algo widening directly follows the transitions,
  //i.e. to connect to states in the tree, we need one witness for the transition and for the widening.

  protected var witnessesMap: Map[S, Map[S, (TransitionWitness[P], WideningWitnessSeq[P])]] = null

  protected def populateWitnessesMap {
    val wWitnesses = wideningWitnesses.toArray(Array.ofDim[WideningWitnessSeq[P]](0))
    wideningWitnesses.clear()
    val wwGroupedByOrigin = wWitnesses.par.groupBy(_.from)

    val tWitnesses = transitionWitnesses.toArray(Array.ofDim[TransitionWitness[P]](0))
    transitionWitnesses.clear()
    val twWithWw = tWitnesses.par.map( tw => {
      val matching = wwGroupedByOrigin(tw.to)
      assert(matching.length == 1)
      (tw, matching.head)
    })
    
    val groupedByOrigin = twWithWw.par.groupBy(_._1.from)
    val groupedByOriginAndResult = groupedByOrigin.map{ case (k, v) =>
      (k, v.groupBy(_._2.to))
    }

    val simplification1 = groupedByOriginAndResult.map{ case (k0, v0) =>
      val v0p = v0.map{ case (k1, v1) =>
        assert(v1.length == 1)
        (k1, v1.head)
      }
      (k0, v0p.seq)
    }

    witnessesMap = simplification1.seq
  }

  //(3)

  import picasso.model.integer._

  protected def collectForwardEdges(tree: KMTree): Seq[(S,S)] = {
    val toChildren = tree.children.map(x => (tree(), x()))
    (toChildren /: tree.children)(_ ++ collectForwardEdges(_))
  }
  
  protected def collectBackwardEdges(tree: KMTree): Seq[(S,S)] = {
    val covered = tree.subsumed.map(x => (tree(), x())).toSeq
    (covered /: tree.children)(_ ++ collectBackwardEdges(_))
  }


  def makeIntegerProgram(tree: KMTree): Program = {
    //all the transitions: what is witnessed + the back edges
    val forwardEdges = collectForwardEdges(tree)
    val backwardEdges = collectBackwardEdges(tree)
    val witnesses = forwardEdges.map{ case (a,b) => witnessesMap(a)(b) }
    val forwardTrs = witnesses.flatMap( transitionForWitness )
    val backwardTrs = backwardEdges.flatMap{ case (a,b) => covering(a,b) }
    val nodesWithBackEdge = backwardEdges.map( p => getPC(p._1)._1 ).toSet
    //if there is a covering edge from a config, we can drop the acceleration edge !
    val forwardTrs2 = forwardTrs.filterNot(t => /*nodesWithBackEdge(t.sourcePC) &&*/ t.comment == "replicating 2" )
    val allTransitions = forwardTrs2 ++ backwardTrs
    //TODO build a graph, get all the simple paths and try to compact the transitions
    //need an initialisation transition (from nothing to the init state)
    val variables = (Set[Variable]() /: allTransitions)(_ ++ _.variables)
    val init = initialize(tree(), variables)
    val initState = init.sourcePC
    new Program(initState, init +: allTransitions)
  }

  //(4) TODO
  def termination(initState: S) = {
    val (_, tree) = computeTree(initState)
    Logger("DBPTermination", LogInfo, "Populating the witness map.")
    populateWitnessesMap
    Logger("DBPTermination", LogNotice, "Extracting numerical abstraction from the KM tree.")
    val program1 = makeIntegerProgram(tree)
    Logger("DBPTermination", LogNotice, "Extraction done. Simplifying ... ")
    val program2 = program1.simplifyForTermination
    (tree, program2)
    //sys.error("TODO print and call ARMC")
  }

}
