package picasso.analysis

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer}
import picasso.model.dbp._

trait DBPTermination[P <: DBCT] extends KarpMillerTree {
  self: DepthBoundedProcess[P] =>

  //(1) compute the cover and extract the transition witnesses
  //(2) build some sensible datastructure out of the witnesses buffers
  //(3) using the witnesses create an integer program ...

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

  protected var witnessesMap: Map[S, Map[S, (TransitionWitness[P], WideningWitnessSeq[P])]]

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

  //TODO (3)
  //what are the states: configuration, not KMTree
  //  for each conf we should associate a set of counters (Map[P#V, String])
  //  then ...
  //how do we go from one state to another:
  // - transition:
  //   -> inhibiting
  //   -> unfolding
  //   -> morphing
  //   -> folding
  // - covering (? similar to folding ?)
  // - widening:
  //   -> replicating
  //   -> folding

  import picasso.model.integer._

  protected def variablesForNodes(conf: S): Map[P#V, Variable] = {
    val nodes = conf.vertices.toSeq
    val pairs = nodes.filter(_.depth > 0).map( x => (x -> Variable(Namer(x.state.toString))))
    pairs.toMap
  }

  //conf -> (PC, node -> var)
  protected val PCs = new java.util.concurrent.ConcurrentHashMap[S, (String, Map[P#V, Variable])]()

  protected def getPC(conf: S): (String, Map[P#V, Variable]) = {
    if (PCs.containsKey(conf)) {
      PCs.get(conf)
    } else {
      val varMap = variablesForNodes(conf)
      PCs.putIfAbsent(conf, (Namer("S_"), varMap))
    }
  }

  protected def getCardinality(map: Map[P#V, Variable], node: P#V): Expression = {
    if (map contains node) {
      map(node)
    } else {
      assert(node.depth == 0)
      Constant(1)
    }
  }

  // summing up the variable and adding constant for non-replicated nodes.
  protected def folding(from: S, folding: Map[P#V, P#V], to: S): Transition = {
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    //invert the folding so that when we look at one node in to, we get all the from nodes that map to it.
    val backwardFolding: Map[P#V, Seq[P#V]] = folding.toSeq.map{ case (a,b) => (b,a) }.groupBy( _._1 ).mapValues( _ map (_._2) )
    val stmts1 = for ( (node, lst) <- backwardFolding ) yield {
       var rhs = lst.map(getCardinality(map1, _)).reduceLeft(Plus(_, _))
       getCardinality(map2, node) match {
         case v @ Variable(_) =>
           Affect(v, Plus(v, rhs))
         case Constant(1) => 
           assert(rhs == Constant(1))
           Skip
         case other =>
           Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    //stmt1 contains the update of the counter into to 'to', now we need statments for the counters of 'from'
    val stmts2 = for ( node <- folding.keys ) yield {
      getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(1) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts = (stmts1 ++ stmts2).toSeq
    new Transition(pc1, pc2, Literal(true), stmts)
  }

  // ...
  //this would be for thomas' improved version of the widening (i.e self loop)
  //another simpler version would be to just have a back edges that transform transfer some of the counters
  protected def replicating(from: S, replicating: Set[P#V], to: S): Transition = {
    sys.error("TODO")
  }
  
  // replicated nodes that disappear are set to 0
  // node from 'from' should be either in 'to' or in 'inhibited'
  protected def inhibiting(from: S, inhibited: Set[P#V], to: S): Transition = {
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    val stmts1 = for ( node <- from.vertices if !inhibited.contains(node)) yield {
      assert(to.vertices contains node)
      getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, getCardinality(map1, node))
         case Constant(1) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts2 = for ( node <- from.vertices ) yield {
      getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(1) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts = (stmts1 ++ stmts2).toSeq
    new Transition(pc1, pc2, Literal(true), stmts)
  }

  // the reverse of folding ...
  protected def unfolding(from: S, morph1: Map[P#V,P#V], to: S, morph2: Map[P#V, P#V]): Transition = {
    //TODO the first step is to reconstruct a mapping from the node of 'to' to the node of 'from'
    sys.error("TODO")
  }

  // ...
  protected def morphing(from: S, morph1: Map[P#V, P#V], tr: T, to: S): Transition = {
    sys.error("TODO")
  }

  def makeIntegerProgram(tree: KMTree): Program = {
    sys.error("TODO")
  }

}
