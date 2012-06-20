package picasso.analysis

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer}
import picasso.model.dbp._
import picasso.graph._
import picasso.model.integer._

trait DBPTerminationCommon[P <: DBCT] extends KarpMillerTree {
  self: DepthBoundedProcess[P] =>

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
      val value = (Namer("S_"), varMap)
      val res = PCs.putIfAbsent(conf, value)
      if (res == null) value else res
    }
  }

  protected def getCardinality(map: Map[P#V, Variable], node: P#V): Expression = {
    if (map contains node) {
      map(node)
    } else {
      assert(node.depth == 0, node)
      Constant(1)
    }
  }

  protected def coverOrFold(from: S, morph: Map[P#V, P#V], to: S): (String, String, Seq[Statement]) = {
    Logger("DBPTermination", LogDebug, "coverOrFold with " + morph)
    assert(from != to)
    assert(morph.keys.forall (from contains _) )
    assert(from.vertices forall (morph contains _) )
    assert(morph.values.forall (to contains _) )
    val morph1 = (from.vertices.map(v => (v, morph.getOrElse(v,v))): Iterable[(P#V,P#V)]).toMap
    assert(morph1.values.forall (to contains _) )
    //assert(from.vertices forall (folding contains _))
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    //invert the folding so that when we look at one node in to, we get all the from nodes that map to it.
    val backwardFolding: Map[P#V, Seq[P#V]] = morph1.toSeq.map{ case (a,b) => (b,a) }.groupBy( _._1 ).mapValues( _ map (_._2) )
    val frame = to.vertices -- backwardFolding.keys
    //assert(to.vertices forall (backwardFolding contains _))
    val stmts1 = for ( (node, lst) <- backwardFolding ) yield {
       var rhs = lst.map(getCardinality(map1, _)).reduceLeft(Plus(_, _))
       getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, rhs)
         case Constant(c) => assert(rhs == Constant(c)); Skip
         case other =>
           Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    //stmt1 contains the update of the counter into to 'to', now we need statments for the counters of 'from'
    val stmts2 = for ( node <- morph1.keys ) yield {
      getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts3 = for (node <- frame) yield {
      getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts = (stmts1 ++ stmts2 ++ stmts3).toSeq
    (pc1, pc2, stmts)
  }

  // summing up the variable and adding constant for non-replicated nodes.
  protected def folding(from: S, folding: Map[P#V, P#V], to: S): Transition = {
    Logger("DBPTermination", LogDebug, "folding transition from " + from +
                                       " to " + to +
                                       "\nfrom.vertices: " + from.vertices +
                                       "\nto.vertices: " + to.vertices)
    val (pc1, pc2, stmts) = coverOrFold(from, folding, to)
    new Transition(pc1, pc2, Literal(true), stmts, "folding")
  }
  
  //send back the counters
  protected def covering(smaller: S, bigger: S): Seq[Transition] = {
    Logger("DBPTermination", LogDebug, "covering transition from " + smaller +
                                       " to " + bigger +
                                       "\nsmaller.vertices: " + smaller.vertices +
                                       "\nbigger.vertices: " + bigger.vertices)
    val morphisms = smaller.morphisms(bigger)(self.stateOrdering)
    val trs = for (m <- morphisms) yield {
      val (pc1, pc2, stmts) = coverOrFold(smaller, m, bigger)
      new Transition(pc1, pc2, Literal(true), stmts, "covering")
    }
    trs.toSeq
  }
  

  //TODO simple version of the replication -> send the counters back
  protected def replicatingSimple(from: S, smaller: S, replicating: Map[P#V, P#V], to: S): Seq[Transition] = {
    Logger("DBPTermination", LogDebug, "replicatingSimple transition from " + from +
                                       " to " + to +
                                       " with " + smaller +
                                       " and " + replicating +
                                       "\nfrom.vertices: " + from.vertices +
                                       "\nto.vertices: " + to.vertices)
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    val (pc3, map3) = getPC(smaller)
    val frame = from.vertices -- replicating.keys
    //first transition: add to the counter
    val stmts1 = for ( (n1, n2) <- replicating) yield {
      getCardinality(map2, n2) match {
        case v @ Variable(_) => Affect(v, getCardinality(map1, n1))
        case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable for "+n2+", found: " + other)
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
         case v @ Variable(_) => Affect(v, getCardinality(map1, node))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts4 = for (node <- frame ) yield {
       getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts = (stmts1 ++ stmts2 ++ stmts3 ++ stmts4).toSeq
    val t1 = new Transition(pc1, pc2, Literal(true), stmts, "replicating 1")
    //second transition: back edge
    val morphisms = smaller.morphisms(to)(self.stateOrdering)
    var trs2 = for( m <- morphisms ) yield {
      val frame = to.vertices -- m.values
      val stmts1 = for ( (n3, n2) <- m) yield {
        getCardinality(map3, n3) match {
          case v @ Variable(_) => Affect(v, getCardinality(map2, n2))
          case Constant(_) => Skip
          case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
        }
      }
      val stmts2 = for ( (n3, n2) <- m) yield {
        getCardinality(map2, n2) match {
          case v @ Variable(_) => {
            getCardinality(map3, n3) match {
              case Variable(_) => Affect(v, Constant(0))
              case c @ Constant(_) => assert(false); Skip
              case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
            }
          }
          case Constant(c) => Skip
          case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
        }
      }
      val stmts3 = for (node <- frame ) yield {
         getCardinality(map2, node) match {
           case v @ Variable(_) => Affect(v, Constant(0))
           case Constant(c) => Skip
           case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
         }
      }
      val lowerBounds = for ( (n3, n2) <- m) yield {
        getCardinality(map2, n2) match {
          case v @ Variable(_) => {
            getCardinality(map3, n3) match {
              case c @ Constant(_) => Some(Leq(c, v))
              case _ => None
            }
          }
          case _ => None
        }
      }
      val guard = ((Literal(true): Condition) /: lowerBounds){
        case (acc, Some(c)) => And(acc,c)
        case (acc, None) => acc
      }
      val stmts = (stmts1 ++ stmts2 ++ stmts3).toSeq
      new Transition(pc2, pc3, guard, stmts, "replicating 2")
    }
    t1 +: trs2.toSeq
  }

  // replicated nodes that disappear are set to 0
  // node from 'from' should be either in 'to' or in 'inhibited'
  protected def inhibiting(from: S, inhibited: Set[P#V], flattening: Map[P#V,P#V], to: S): Transition = {
    Logger("DBPTermination", LogDebug, "inhibited transition from " + from +
                                       " to " + to +
                                       " with " + inhibited +
                                       "\nfrom.vertices: " + from.vertices +
                                       "\nto.vertices: " + to.vertices +
                                       "\nflattening: " + flattening.mkString(", "))
    assert(from != to)
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    val stmts1 = for ( node1 <- from.vertices if !inhibited.contains(node1) ) yield {
      val node2 = flattening(node1)
      assert(to contains node2)
      getCardinality(map2, node2) match {
         case v @ Variable(_) => Affect(v, getCardinality(map1, node1))
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
    new Transition(pc1, pc2, Literal(true), stmts, "inhibiting")
  }

  // the reverse of folding ...
  //revMorph is a mapping from the node of 'to' to the node of 'from'
  //TODO when unfolding a component, do we need to keep some more information (i.e. unfold the same as or at least as much as ...)
  protected def unfolding(from: S, revMorph: Map[P#V,P#V], to: S): Transition = {
    Logger("DBPTermination", LogDebug, "unfolding transition from " + from +
                                       " to " + to +
                                       " with " + revMorph +
                                       "\nfrom.vertices: " + from.vertices +
                                       "\nto.vertices: " + to.vertices)
    // Way to encode the unfolding
    // part 1: conservation -> the sum before = the sum after
    // part 2: the variance -> the higher depth node decreases, the rest increase
    // ...
    assert(from != to)
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)

    //reverse the unfolding
    val frame = to.vertices -- revMorph.keys
    assert(frame forall (from contains _) )
    val revMorph2 = revMorph ++ frame.map(x => (x,x))
    val backwardUnFolding: Map[P#V, Seq[P#V]] = revMorph2.toSeq.map{ case (a,b) => (b,a) }.groupBy( _._1 ).mapValues( _ map (_._2) )
    assert(to.vertices forall (revMorph2 contains _))
    assert(from.vertices forall (backwardUnFolding contains _))

    val stmts1 = for ( (node, lst) <- backwardUnFolding ) yield {
       var lhs = lst.map(getCardinality(map2, _)).reduceLeft(Plus(_, _))
       getCardinality(map1, node) match {
         case v @ Variable(_) =>
           val rhs = lst.filter(_.depth > 0).map(getCardinality(map2, _)).reduceLeft(Plus(_, _))
           Relation(lhs, Plus(rhs, v))
         case Constant(1) => assert(lhs == Constant(1)); Skip
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
    // the variance
    val varies = backwardUnFolding.filter(_._2.length > 1)
    val increases = varies.flatMap{ case (node, lst) =>
      lst.filter(n2 => n2.depth < node.depth)
    }
    val decreases = varies.map{ case (node, lst) =>
      val candidates = lst.filter(n2 => n2.depth >= node.depth)
      assert(candidates.size == 1)
      (node, candidates.head)
    }
    val variance1 = increases.map( n => {
      getCardinality(map2, n) match {
         case v1 @ Variable(_) => Assume(Leq(Constant(0), v1))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    })
    val variance2 = decreases.flatMap{ case (nOld, nNew) => 
      getCardinality(map2, nNew) match {
         case v1 @ Variable(_) =>
           getCardinality(map1, nOld) match {
             case v2 @ Variable(_) => Seq( Assume(Leq(Constant(0), v1)), Variance(v1, v2, false, false) )
             case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
           }
         case Constant(c) => Seq()
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    // what is needed for the unfolding
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
    val stmts = (stmts1 ++ stmts2 ++ variance1 ++ variance2).toSeq
    new Transition(pc1, pc2, guard, stmts, "unfolding")
  }

  //Actually, there is nothing to do here.
  //Just check that the transition does not change replicated things and transfer the frame
  protected def morphing(from: S, frame: Map[P#V, P#V], tr: T, to: S): Transition = {
    Logger("DBPTermination", LogDebug, "morphing transition from " + from +
                                       " to " + to +
                                       " with " + frame +
                                       "\nfrom.vertices: " + from.vertices +
                                       "\nto.vertices: " + to.vertices)
    assert(from != to)
    //assert(morph1.values.forall(_.depth == 0))
    assert(frame.forall{case (a,b) => a.depth == b.depth})
    assert(tr.lhs.vertices.forall(_.depth == 0))
    assert(tr.rhs.vertices.forall(_.depth == 0))
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    val changing = from.vertices -- frame.keys
    assert(changing forall (_.depth == 0))
    val stmts1 = for ((n1,n2) <- frame ) yield {
       getCardinality(map2, n2) match {
         case v @ Variable(_) => Affect(v, getCardinality(map1, n1))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts2 = for ((n1,n2) <- frame) yield {
       getCardinality(map1, n1) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts = (stmts1 ++ stmts2).toSeq
    new Transition(pc1, pc2, Literal(true), stmts, "morphing, " + tr.id)
  }

  protected val emptyConf = DepthBoundedConf.empty[P]

  protected def initialize(init: S, allVariables: Set[Variable]): Transition = {
    val (pc0, _) = getPC(emptyConf)
    val (pc1, map1) = getPC(init)
    //the inital transition is similar to the widening transitions ... 
    val components: DiGraph[GT.ULGT{type V = Set[P#V]}] = init.decomposeInDisjointComponents
    val cmpId = components.vertices.zipWithIndex.toMap
    val nodeToCmpId = (cmpId.flatMap{ case (seq, id) => seq.map(x => (x, id)) } : Iterable[(P#V, Int)]).toMap
    val accelerationVariables = cmpId.map{ case (k,v) => (v, Variable("init_" + v)) }
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
    val stmts = (declare ++ assumes1 ++ assumes2 ++ stmts1 ++ stmts2).toSeq
    new Transition(pc0, pc1, Literal(true), stmts, "initialize")
  }

  protected def isUnfoldingTrivial(from: S, revMorph: Map[P#V,P#V], to: S) = {
    if (from == to) {
      assert(revMorph.isEmpty)
      true
    } else {
      false
    }
  }
  protected def isInhibitingTrivial(from: S,  inhibited: Set[P#V], flatten: Map[P#V,P#V], to: S) = {
    if (from == to) {
      assert(inhibited.isEmpty && flatten.isEmpty)
      true
    } else {
      false
    }
  }
  protected def isFoldingTrivial(from: S, folding: Map[P#V,P#V], to: S) = {
    if (from == to) {
      assert(folding.isEmpty || folding.forall{ case (a,b) => a == b})
      true
    } else {
      false
    }
  }
  protected def isMorphingTrivial(from: S, frame: Map[P#V, P#V], tr: T, to: S) = {
    assert(from != to)
    false
  }
  protected def isReplicationTrivial(from: S, smaller: S, replicating: Map[P#V, P#V], to: S) = {
    assert(from != to)
    false
  }

  protected def transitionForWitness1(witness: TransitionWitness[P]): Seq[Transition] = {
    val t1 =
      if (isUnfoldingTrivial(witness.from, witness.unfolding, witness.unfolded)) None
      else Some(unfolding(witness.from, witness.unfolding, witness.unfolded))
    val t2 =
      if (isInhibitingTrivial(witness.unfolded, witness.inhibitedNodes, witness.inhibitedFlattening, witness.inhibited)) None
      else Some(inhibiting(witness.unfolded, witness.inhibitedNodes, witness.inhibitedFlattening, witness.inhibited))
    val t3 =
      if (isMorphingTrivial(witness.inhibited, witness.post, witness.transition, witness.unfoldedAfterPost)) None
      else Some(morphing(witness.inhibited, witness.post, witness.transition, witness.unfoldedAfterPost))
    val t4 =
      if (isFoldingTrivial(witness.unfoldedAfterPost, witness.folding, witness.to)) None
      else Some(folding(witness.unfoldedAfterPost, witness.folding, witness.to))
    Seq(t1, t2, t3, t4).flatten
  }
  
  protected def transitionForWitness2(witness: WideningWitness[P]): Seq[Transition] = {
    val t1 =
      if (isReplicationTrivial(witness.bigger, witness.smaller, witness.replicated, witness.unfoldedResult)) Seq[Transition]()
      else replicatingSimple(witness.bigger, witness.smaller, witness.replicated, witness.unfoldedResult)
    val t2 =
      if (isFoldingTrivial(witness.unfoldedResult, witness.folding, witness.result)) Seq[Transition]()
      else Seq(folding(witness.unfoldedResult, witness.folding, witness.result))
    t1 ++ t2
  }

  protected def transitionForWitness(witness: (TransitionWitness[P], WideningWitnessSeq[P])): Seq[Transition] = {
    transitionForWitness1(witness._1) ++ witness._2.sequence.flatMap(transitionForWitness2)
  }

  //this method assumes that each loc has its own variables (not true after the simplification)
  protected def simplifyPath(trs: Seq[Transition]): Seq[Transition] = {
    //reduce the number of #transitions and variables
    if (trs.size > 1) {
      //1 -> reduce the number of variables without changing the first and the last part
      //conflicts are variables that are at one loc, between locs, no conflict
      val varsAtLoc = trs.map(_.readVariables) //this ignores the last loc
      val conflicts = (DiGraph.empty[GT.ULGT{type V = Variable}] /: varsAtLoc)( (acc, vs) => {
        val edges = for (x <- vs; y <- vs if x != y) yield (x, (), y)
        acc ++ edges
      })
      def affinity(v1: Variable, v2: Variable) = Misc.commonPrefix(v1.name, v2.name)
      val largeClique = varsAtLoc.maxBy(_.size)
      val coloring = conflicts.smallColoring(affinity, largeClique)
      val headVariables = varsAtLoc.head //these variables should be preserved
      val trs2 = (trs /: coloring)( (acc, grp) => {
        if (grp.size > 1) {
          val newVar = grp.find(headVariables contains _).getOrElse(grp.head)
          acc.map( _.mergeVariables(grp, newVar) )
        } else {
          acc
        }
      })
      //2 -> compact
      val trs3 = Transition.compact(trs2)
      //TODO
      val trsNew = trs3
      //3 -> useless split
      //4 -> prune assume
      //5 -> loop ?
      //TODO assert that the variables at both ends are the same
      //println("before = " + trs.size + ", after = " + trsNew.size)
      trsNew
    } else {
      trs
    }
  }


}
