package picasso.analysis

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc, Namer, Config}
import picasso.model.dbp._
import picasso.graph._
import picasso.math.DownwardClosedSet
import picasso.model.integer._
import scala.collection.parallel.{ParIterable, ParSeq}

trait DBPTermination[P <: DBCT] {
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

  //TODO move to Transition2/Program2

  protected def variablesForNodes(conf: S): Map[P#V, Variable] = {
    val needed = conf.vertices.toSeq
    val pairs = needed.map( x => (x -> Variable(Namer(x.state.toString))))
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
    map(node)
  }

  //TODO guardForConcreteNode: just the nodes we care about ...
  protected def guardForConcreteNode(s: S, acc: Condition = Literal(true)): Condition = {
    val (_, map) = getPC(s)
    val concreteNodes = s.vertices.view.filter(_.depth == 0)
    val cnd = concreteNodes.map(n => Eq(getCardinality(map, n), Constant(1)))
    And(acc :: cnd.toList)
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
         case other =>
           Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    //stmt1 contains the update of the counter into to 'to', now we need statments for the counters of 'from'
    val stmts2 = for ( node <- morph1.keys ) yield {
      getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts3 = for (node <- frame) yield {
      getCardinality(map2, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
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
    new Transition(pc1, pc2, guardForConcreteNode(from), stmts, "folding")
  }
  
  protected def covering(smaller: S, morph: Map[P#V, P#V], bigger: S): Transition = {
    Logger("DBPTermination", LogDebug, "covering transition from " + smaller +
                                       " to " + bigger +
                                       "\nsmaller.vertices: " + smaller.vertices +
                                       "\nbigger.vertices: " + bigger.vertices)
    val (pc1, pc2, stmts) = coverOrFold(smaller, morph, bigger)
    new Transition(pc1, pc2, guardForConcreteNode(smaller), stmts, "covering")
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
      new Transition(pc1, pc2, guardForConcreteNode(smaller), stmts, "covering")
    }
    trs.toSeq
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
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts2 = for ( node <- from.vertices ) yield {
      getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    val stmts = (stmts1 ++ stmts2).toSeq
    new Transition(pc1, pc2, guardForConcreteNode(from), stmts, "inhibiting")
  }

  //TODO when unfolding a component, do we need to keep some more information (i.e. unfold the same as or at least as much as ...)
  protected def unfolding(from: S, backwardUnFolding: Map[P#V, Seq[P#V]], to: S): Transition = {
    Logger("DBPTermination", LogDebug, "unfolding transition from " + from +
                                       " to " + to +
                                       " with " + backwardUnFolding +
                                       "\nfrom.vertices: " + from.vertices +
                                       "\nto.vertices: " + to.vertices)
    // Way to encode the unfolding
    // part 1: conservation -> the sum before = the sum after
    // part 2: the variance -> the higher depth node decreases, the rest increase
    // ...
    assert(from != to)
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)

    assert({val range = backwardUnFolding.values.flatten.toSet; to.vertices forall (range contains _)})
    assert(from.vertices forall (backwardUnFolding contains _))

    val stmts1 = for ( (node, lst) <- backwardUnFolding ) yield {
       val (concrete, abstr) = lst.partition(_.depth == 0)
       val concreteUpd = concrete.map( getCardinality(map2, _) match {
         case v @ Variable(_) => Affect(v, Constant(1))
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       })
       val abstrUpd = if (!abstr.isEmpty) {
         val lhs = abstr.map(getCardinality(map2, _)).foldLeft(Constant(concrete.size): Expression)(Plus(_, _))
         getCardinality(map1, node) match {
           case v @ Variable(_) => Relation(lhs, v)
           case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
         }
       } else Skip
       concreteUpd :+ abstrUpd
    }
    val stmts2 = for ( node <- backwardUnFolding.keys ) yield {
      getCardinality(map1, node) match {
         case v @ Variable(_) => Affect(v, Constant(0))
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
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
      }
    }
    // what is needed for the unfolding
    val lowerBounds = for ( (node, lst) <- backwardUnFolding ) yield {
       val concrete = lst.filter(_.depth == 0)
       getCardinality(map1, node) match {
         case v @ Variable(_) => Leq(Constant(concrete.size), v)
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    //TODO make sure we catch everyone ...
    val guard = And(guardForConcreteNode(from) :: lowerBounds.toList)
    val stmts = (stmts1.flatten ++ stmts2 ++ variance1 ++ variance2).toSeq
    new Transition(pc1, pc2, guard, stmts, "unfolding")
  }

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
    //assert(tr.rhs.vertices.forall(_.depth == 0))
    val (pc1, map1) = getPC(from)
    val (pc2, map2) = getPC(to)
    val disappearing = from.vertices -- frame.keys
    val appearing = to.vertices -- frame.values
    assert(disappearing forall (_.depth == 0))
    //assert(appearing forall (_.depth == 0))
    if (appearing exists (_.depth > 0)) Logger("DBPTermination", LogWarning, "appearing with depth > 0")
    val stmts1 = for (n <- disappearing) yield {
       getCardinality(map1, n) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts2 = for (n <- appearing) yield {
       getCardinality(map2, n) match {
         case v @ Variable(_) => if (n.depth == 0) Affect(v, Constant(1)) else Assume(Leq(Constant(0), v))
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts3 = for ((n1,n2) <- frame) yield {
       getCardinality(map2, n2) match {
         case v @ Variable(_) => Affect(v, getCardinality(map1, n1))
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts4 = for ((n1,n2) <- frame) yield {
       getCardinality(map1, n1) match {
         case v @ Variable(_) => Affect(v, Constant(0))
         case Constant(c) => Skip
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    val stmts = (stmts1 ++ stmts2 ++ stmts3 ++ stmts4).toSeq
    new Transition(pc1, pc2, guardForConcreteNode(from), stmts, "morphing, " + tr.id)
  }

  protected val emptyConf = DepthBoundedConf.empty[P]

  protected def initialize(init: S): Transition2 = {
    val (pc0, _) = getPC(emptyConf)
    val (pc1, map1) = getPC(init)
    //the inital transition is similar to the widening transitions ... 
    val stmts = for (node <- init.vertices) yield {
       getCardinality(map1, node) match {
         case v @ Variable(_) =>
           if (node.depth == 0) Affect(v, Constant(1))
           else Assume(Leq(Constant(0),v))
         case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Variable, found: " + other)
       }
    }
    Transition2(new Transition(pc0, pc1, Literal(true), stmts.toSeq, "initialize"))
  }

  protected def transitionForWitness(witness: TransitionWitness[P]): Seq[Transition] = {
    val t1 =
      if (witness.isUnfoldingTrivial) None
      else Some(unfolding(witness.from, witness.reversedUnfolding, witness.unfolded))
    val t2 =
      if (witness.isInhibitingTrivial) None
      else Some(inhibiting(witness.unfolded, witness.inhibitedNodes, witness.inhibitedFlattening, witness.inhibited))
    val t3 =
      if (witness.isPostTrivial) None
      else Some(morphing(witness.inhibited, witness.post, witness.transition, witness.unfoldedAfterPost))
    val t4 =
      if (witness.isFoldingTrivial) None
      else Some(folding(witness.unfoldedAfterPost, witness.folding, witness.to))
    Seq(t1, t2, t3, t4).flatten
  }
  
  //assumes the transitions also contains the frame
  protected def simplifyPathByQE(trs: Seq[Transition]): Seq[Transition2] = {
    val tr2s = trs.map(Transition2.apply)
    Transition2.compact(tr2s)
  }

  ///////////////
  //The program//
  ///////////////

  protected def makeTransitions(tg: EdgeLabeledDiGraph[TransitionsGraphFromCover.TG[P]]): ParIterable[Transition2] = {
    import TransitionsGraphFromCover._
    //TODO the edges should go by pairs: transition + covering
    //the simplification might be more efficient if the first pass simplify both.
    //TODO some check to be sure the graph has the right form ?
    tg.vertices.toSeq.par.flatMap( v1 => {
      tg.outEdges(v1).flatMap{
        case (Transition(witness), succs) =>
          succs.toSeq.flatMap(v2 => {
            val out = tg.outEdges(v2)
            if (out.size == 1) {
              out.head match {
                case (Covering(m), targets) => 
                  Logger.assert(targets.size == 1, "DBPTermination", "Expected single successor: " + targets)
                  simplifyPathByQE( transitionForWitness(witness) :+ covering(v2, m, targets.head))
                case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Covering, found: " + other)
              }
            } else {
              val p1 = simplifyPathByQE(transitionForWitness(witness))
              val p2s = out.map{
                case (Covering(m), targets) => 
                  Logger.assert(targets.size == 1, "DBPTermination", "Expected single successor: " + targets)
                  Transition2(covering(v2, m, targets.head))
                case other => Logger.logAndThrow("DBPTermination", LogError, "Expected Covering, found: " + other)
              }
              p2s ++ p1
            }
          })
        case _ => None
      }
    })
  }

  def makeIntegerProgram(cover: DownwardClosedSet[S]): Program2 = {
    val tg = TransitionsGraphFromCover(this, cover)
    val trs = makeTransitions(tg)
    val variables = (Set[Variable]() /: trs)(_ ++ _.variables)
    val initials = for (init <- cover.basis.toSeq.par) yield initialize(init)
    val initState = initials.head.sourcePC
    new Program2(initState, (initials ++ trs): ParSeq[Transition2] )
  }
  //TODO generate directly the new transition without going through the old one.

  def termination(cover: DownwardClosedSet[S]) = {
    Logger("DBPTermination", LogNotice, "Extracting numerical abstraction from the cover.")
    val program1 = makeIntegerProgram(cover)
    Logger("DBPTermination", LogNotice, "Extraction done. Simplifying ... ")
    program1.simplifyForTermination
  }
  
}
