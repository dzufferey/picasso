package picasso.analysis

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer}
import picasso.model.dbp._
import picasso.graph._

trait DBPTermination[P <: DBCT] extends KarpMillerTree {
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

  //(3)
  //what are the states: configuration, not KMTree
  //  for each conf we should associate a set of counters (Map[P#V, String])
  //  then ...
  //how do we go from one state to another:
  // - transition:
  //   -> inhibiting
  //   -> unfolding
  //   -> morphing
  //   -> folding
  // - covering (similar to folding)
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
    assert(from.vertices forall (folding contains _))
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    //invert the folding so that when we look at one node in to, we get all the from nodes that map to it.
    val backwardFolding: Map[P#V, Seq[P#V]] = folding.toSeq.map{ case (a,b) => (b,a) }.groupBy( _._1 ).mapValues( _ map (_._2) )
    assert(to.vertices forall (backwardFolding contains _))
    val stmts1 = for ( (node, lst) <- backwardFolding ) yield {
       var rhs = lst.map(getCardinality(map1, _)).reduceLeft(Plus(_, _))
       getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, Plus(v, rhs))
         case Constant(1) => assert(rhs == Constant(1)); Skip
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
  //this should be for thomas' improved version of the widening (i.e self loop)
  //another simpler version would be to just have a back edges that transform transfer some of the counters
  protected def replicating(from: S, replicating: Map[P#V,P#V], to: S): Transition = {
    sys.error("TODO: this is wrong -> nothing ever decreasing ! (nor is it a loop)")  //TODO
    //the thing is that we are starting with a small configuration and replicating nodes give a bigger config.
    //for depth 1, we are adding to the replicated nodes x > 0 ,
    //for depth 2, the increase is y >= x
    //for depth 3, z >= y
    // ...
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    val frame = from.vertices -- replicating.keys
    //we need to get the components in 'to' to know the inequalities between increases
    val components: DiGraph[GT.ULGT{type V = Set[P#V]}] = to.decomposeInDisjointComponents
    val cmpId = components.vertices.zipWithIndex.toMap
    val nodeToCmpId = (cmpId.flatMap{ case (seq, id) => seq.map(x => (x, id)) } : Iterable[(P#V, Int)]).toMap
    val accelerationVariables = cmpId.map{ case (k,v) => (v, Variable("widen_" + v)) }
    //now make the statments
    val declare = accelerationVariables.values.map( v => Transient(v) )
    val assumes1 = for ( (_,v) <- accelerationVariables) yield Assume(Leq(Constant(0), v))
    val edges: Iterable[(Set[P#V],Unit,Set[P#V])] = components.edges
    val assumes2 = for ( (c1, _, c2) <- edges ) yield {
      val v1 = accelerationVariables(cmpId(c1))
      val v2 = accelerationVariables(cmpId(c2))
      Assume(Leq(v1, v2))
    }
    val stmts1 = for ( (n1, n2) <- replicating) yield {
      getCardinality(map2, n2) match {
        case v @ Variable(_) => Affect(v, Plus(v, Plus( accelerationVariables(nodeToCmpId(n2)), getCardinality(map1, n1))))
        case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts2 = for ( (n1, _) <- replicating) yield {
      getCardinality(map1, n1) match {
        case v @ Variable(_) => Affect(v, Constant(0))
        case Constant(c) => Skip
        case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts3 = for (node <- frame ) yield {
       getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, Plus(v, getCardinality(map1, node)))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts = (declare ++ assumes1 ++ assumes2 ++ stmts1 ++ stmts2 ++ stmts3).toSeq
    new Transition(pc1, pc2, Literal(true), stmts)
  }

  //send back the counters
  protected def covering(smaller: S, bigger: S): Seq[Transition] = {
    val (pc1, map1) = getPC(smaller)
    val (pc2, map2) = getPC(bigger)
    val morphisms = smaller.morphisms(bigger)(self.stateOrdering)
    val trs = for (m <- morphisms) yield {
      assert(smaller.vertices forall (m contains _))
      val backwardM: Map[P#V, Seq[P#V]] = m.toSeq.map{ case (a,b) => (b,a) }.groupBy( _._1 ).mapValues( _ map (_._2) )
      val stmts1 = for ((node, lst) <- backwardM) yield {
        var rhs = lst.map(getCardinality(map1, _)).reduceLeft(Plus(_, _))
        getCardinality(map2, node) match {
          case v @ Variable(_) => Affect(v, Plus(v, rhs))
          case Constant(c) => assert(rhs == Constant(c)); Skip
          case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
        }
      }
      val stmts2 = for (node <- smaller.vertices) yield {
         getCardinality(map2, node) match {
           case v @ Variable(_) => Affect(v, Constant(0))
           case Constant(c) => Skip
           case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
         }
      }
      val stmts = (stmts1 ++ stmts2).toSeq
      new Transition(pc1, pc2, Literal(true), stmts)
    }
    trs.toSeq
  }
  
  // replicated nodes that disappear are set to 0
  // node from 'from' should be either in 'to' or in 'inhibited'
  protected def inhibiting(from: S, inhibited: Set[P#V], to: S): Transition = {
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    val stmts1 = for ( node <- from.vertices if !inhibited.contains(node)) yield {
      assert(to contains node)
      getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, Plus(v, getCardinality(map1, node)))
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
  //revMorph is a mapping from the node of 'to' to the node of 'from'
  protected def unfolding(from: S, revMorph: Map[P#V,P#V], to: S): Transition = {
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    //reverse the unfolding
    val backwardUnFolding: Map[P#V, Seq[P#V]] = revMorph.toSeq.map{ case (a,b) => (b,a) }.groupBy( _._1 ).mapValues( _ map (_._2) )
    assert(to.vertices forall (revMorph contains _))
    assert(from.vertices forall (backwardUnFolding contains _))
    val stmts1 = for ( (node, lst) <- backwardUnFolding ) yield {
       var rhs = lst.map(getCardinality(map2, _)).reduceLeft(Plus(_, _))
       getCardinality(map1, node) match {
         case v @ Variable(_) => Relation(rhs, v)
         case Constant(1) => assert(rhs == Constant(1)); Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts2 = for ( node <- backwardUnFolding.keys ) yield {
      getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(1) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val lowerBounds = for ( (node, lst) <- backwardUnFolding ) yield {
       var rhs = lst.map(getCardinality(map2, _))
       var constants = rhs.map{ case Constant(c) => c; case _ => 0 }
       val sum = ( 0 /: constants)(_ + _)
       getCardinality(map1, node) match {
         case v @ Variable(_) => Leq(Constant(sum), v)
         case Constant(c) => assert(c == sum); Literal(true)
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val guard = ((Literal(true): Condition) /: lowerBounds)(And(_,_))
    val stmts = (stmts1 ++ stmts2).toSeq
    new Transition(pc1, pc2, guard, stmts)
  }

  //Actually, there is nothing to do here.
  //Just check that the transition does not change replicated things and transfer the frame
  protected def morphing(from: S, morph1: Map[P#V, P#V], tr: T, to: S): Transition = {
    assert(morph1.values.forall(_.depth == 0))
    assert(tr.lhs.vertices.forall(_.depth == 0))
    assert(tr.rhs.vertices.forall(_.depth == 0))
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    val frame = from.vertices -- morph1.keys
    val stmts1 = for (node <- frame ) yield {
       getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, Plus(v, getCardinality(map1, node)))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts2 = for (node <- frame) yield {
       getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts = (stmts1 ++ stmts2).toSeq
    new Transition(pc1, pc2, Literal(true), stmts)
  }

  protected def initialize(init: S, allVariables: Set[Variable]): Transition = {
    val (pc0, _) = getPC(DepthBoundedConf.empty[P])
    val (pc1, map1) = getPC(init)
    //the inital transition is similar to the widening transitions ... 
    val components: DiGraph[GT.ULGT{type V = Set[P#V]}] = init.decomposeInDisjointComponents
    val cmpId = components.vertices.zipWithIndex.toMap
    val nodeToCmpId = (cmpId.flatMap{ case (seq, id) => seq.map(x => (x, id)) } : Iterable[(P#V, Int)]).toMap
    val accelerationVariables = cmpId.map{ case (k,v) => (v, Variable("widen_" + v)) }
    //now make the statments
    val declare = accelerationVariables.values.map( v => Transient(v) )
    val assumes1 = for ( (_,v) <- accelerationVariables) yield Assume(Leq(Constant(0), v))
    val edges: Iterable[(Set[P#V],Unit,Set[P#V])] = components.edges
    val assumes2 = for ( (c1, _, c2) <- edges ) yield {
      val v1 = accelerationVariables(cmpId(c1))
      val v2 = accelerationVariables(cmpId(c2))
      Assume(Leq(v1, v2))
    }
    val stmts1 = for (node <- init.vertices) yield {
       getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, accelerationVariables(nodeToCmpId(node)))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val zeroVars = allVariables -- map1.values
    val stmts2 = for (v <- zeroVars) yield Affect(v, Constant(0))
    val stmts = (stmts1 ++ stmts2).toSeq
    new Transition(pc0, pc1, Literal(true), stmts)
  }

  protected def collectForwardEdges(tree: KMTree): Seq[(S,S)] = {
    val toChildren = tree.children.map(x => (tree(), x()))
    (toChildren /: tree.children)(_ ++ collectForwardEdges(_))
  }
  
  protected def collectBackwardEdges(tree: KMTree): Seq[(S,S)] = {
    val covered = tree.subsumed.map(x => (tree(), x())).toSeq
    (covered /: tree.children)(_ ++ collectBackwardEdges(_))
  }

  protected def transitionForWitness1(witness: TransitionWitness[P]): Seq[Transition] = {
    Seq(
      unfolding(witness.from, witness.unfolding, witness.unfolded),
      inhibiting(witness.unfolded, witness.inhibitedNodes, witness.inhibited),
      morphing(witness.inhibited, witness.post, witness.transition, witness.unfoldedAfterPost),
      folding(witness.unfoldedAfterPost, witness.folding, witness.to)
    )
  }
  
  protected def transitionForWitness2(witness: WideningWitness[P]): Seq[Transition] = {
    Seq( replicating(witness.bigger, witness.replicated, witness.unfoldedResult),
         folding(witness.unfoldedResult, witness.folding, witness.result) )
  }

  protected def transitionForWitness(witness: (TransitionWitness[P], WideningWitnessSeq[P])): Seq[Transition] = {
    transitionForWitness1(witness._1) ++ witness._2.sequence.flatMap(transitionForWitness2)
  }

  def makeIntegerProgram(tree: KMTree): Program = {
    //all the transitions: what is witnessed + the back edges
    val forwardEdges = collectForwardEdges(tree)
    val backwardEdges = collectBackwardEdges(tree)
    val witnesses = forwardEdges.map{ case (a,b) => witnessesMap(a)(b) }
    val forwardTrs = witnesses.flatMap( transitionForWitness )
    val backwardTrs = backwardEdges.flatMap{ case (a,b) => covering(a,b) }
    val allTransitions = forwardTrs ++ backwardTrs
    //need an initialisation transition (from nothing to the init state)
    val variables = (Set[Variable]() /: allTransitions)(_ ++ _.variables)
    val init = initialize(tree(), variables)
    val initState = new State(init.sourcePC, Map())
    new Program(initState, init +: allTransitions)
  }

  //(4) TODO
  def termination(initState: S) = {
    val (_, tree) = computeTree(initState)
    val program = makeIntegerProgram(tree)
    sys.error("TODO print and call ARMC")
  }

}
