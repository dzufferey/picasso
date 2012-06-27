package picasso.model.integer
  
import scala.collection.GenSeq
import picasso.graph._
import picasso.utils._

  //what is an ARMC/T2/integer program:
  // program location
  // variables
  // transition (var updates for T2, set of constraints for ARMC)
  // a start location
  // cutpoints (for ARMC)
  //the simplest thing might be to have somthing between T2 and ARMC:
  // get updates like T2, but with an all at the same time semantics like ARMC.

/** Integer Program.
 *  Integer program are use during the termination proof of DBP.
 *  Right now their purpose is just these termination check (not safety).
 */
class Program(initPC: String, trs: GenSeq[Transition]) extends picasso.math.TransitionSystem {
  
  type S = State
  
  //transition type
  type T = Transition

  def initialPC = initPC

  def transitions: GenSeq[T] = trs

  lazy val pcs = (Set(initPC) /: trs)((acc, t) => acc + t.sourcePC + t.targetPC)

  lazy val variables: Set[Variable] = {
    trs.aggregate(Set[Variable]())(_ ++ _.variables, _ ++ _)
  }

  def printForARMC(writer: java.io.BufferedWriter) {
    ARMCPrinter(writer, this)
    writer.flush
  }
  
  def printForARMC: String = {
    val str = new java.io.StringWriter()
    val writer = new java.io.BufferedWriter(str)
    printForARMC(writer)
    writer.close
    str.toString
  }
  
  def printForQARMC(writer: java.io.BufferedWriter) {
    QARMCPrinter(writer, this)
    writer.flush
  }

  def printForQARMC: String = {
    val str = new java.io.StringWriter()
    val writer = new java.io.BufferedWriter(str)
    printForQARMC(writer)
    writer.close
    str.toString
  }
  
  /** try to simplify the program while preserving (non)termination. */
  def simplifyForTermination = {
    //repeat a few time ...
    var p = this
    for (i <- 0 until 2) {
      p = p.simplifyForTermination1
    }
    p
  }
  
  def simplifyForTermination1 = {
    Logger("integer.Program", LogDebug, "unsimplified program:")
    Logger("integer.Program", LogDebug, writer => printForQARMC(writer) )
    Logger("integer.Program", LogInfo, "propagating constants.")
    val p2 = this.propagateCst
    Logger("integer.Program", LogDebug, writer => p2.printForQARMC(writer) )
    Logger("integer.Program", LogInfo, "merging variables.")
    val p4 = p2.reduceNumberOfVariables
    Logger("integer.Program", LogDebug, writer => p4.printForQARMC(writer) )
    Logger("integer.Program", LogInfo, "compacting transitions.")
    val p5 = p4.compactPath
    Logger("integer.Program", LogDebug, writer => p5.printForQARMC(writer) )
    Logger("integer.Program", LogInfo, "removing useless split.")
    val p6 = p5.lookForUselessSplitting
    Logger("integer.Program", LogDebug, writer => p6.printForQARMC(writer) )
    Logger("integer.Program", LogInfo, "pruning Assume.")
    val p7 = p6.pruneAssumes
    Logger("integer.Program", LogDebug, writer => p7.printForQARMC(writer) )
    Logger("integer.Program", LogDebug, writer => p7.reflow.printForQARMC(writer) ) //TODO
    p7
  }

  /** not only propagate 0, but all the constants (especially 1) */
  def propagateCst = {

    //type of the abstract domain: Map[Variable, Option[Int]]
    //None means it is not cst
    //Some(i) means it has value i
    //not in the map means we don't know

    val allVars = variables
    def default(s: String) = {
      if (s == initPC) Map[Variable,Option[Int]]( allVars.toSeq.map( _ -> None) :_* )
      else Map[Variable,Option[Int]]()
    }

    def transfer(cstMap: Map[Variable,Option[Int]], t: Transition): Map[Variable,Option[Int]] = {
      val knows: Iterable[(Variable, Option[Int])] = t.simpleUpdates.flatMap{ case (v, (lst, c)) =>
        if (lst forall (cstMap contains _)) { //means we have enough info
          Some(
            v -> ((Some(c.i): Option[Int]) /: lst)( (acc, v2) => acc.flatMap(i => cstMap(v2).map(j => i + j)))
          )
        } else {
          None
        }
      }
      val complexUpdate = t.updatedVars.filterNot(t.simpleUpdates contains _).map( _ -> None )
      val frame: Map[Variable,Option[Int]] = cstMap -- t.updatedVars
      frame ++ knows ++ complexUpdate
    }

    def join(a: Map[Variable,Option[Int]], b: Map[Variable,Option[Int]]) = {
      val allKeys = a.keySet ++ b.keySet
      val all = allKeys.view.map( v => {
        val rhs = if(a.contains(v) && b.contains(v)) {
          (a(v), b(v)) match {
            case (Some(i1), Some(i2)) => if (i1 == i2) Some(i1) else None
            case (_,_) => None
          }
        } else {
          a.getOrElse(v, b(v))
        }
        (v -> rhs)
      })
      all.toMap
    }

    def cover(a: Map[Variable,Option[Int]], b: Map[Variable,Option[Int]]) = {
      //all keys of b shoud be in a and they should be equal ...
      b forall { case (k,v) => a.contains(k) && (a(k).isEmpty || a(k) == v) }
    }

    val map = cfa.aiFixpoint(transfer, join, cover, default)
    Logger("integer.Program", LogDebug, "propagateCst: " + map)


    val trs2 = trs.par.map(t => {
      val preSubst = map(t.sourcePC).flatMap{ case (k, v) => v.map(i => (k, Constant(i))) }
      t.alphaPre(preSubst).leaner
    })
    new Program(initPC, trs2)
    
  }

  def reduceNumberOfVariables = {
    //if two variables are not live at the same moment, we can merge them!
    val groups = computeVariableMergeApprox
    val trs2 = (trs /: groups)( (trs, grp) => mergeVariables(grp, trs) )
    val p2 = new Program(initPC, trs2)
    Logger("integer.Program", LogInfo, "reduceNumberOfVariables: #variables before = " + variables.size + ", after = " + p2.variables.size)
    p2.renameVariables
  }

  /** create shorter names for the variables */
  def renameVariables = {
    val namer = new Namer
    val subst = variables.map(v => (v, Variable(namer("X")) ) ).toMap
    val trs2 = trs.map(_.alpha(subst))
    new Program(initPC, trs2)
  }

  protected def cfa: EdgeLabeledDiGraph[GT.ELGT{type V = String; type EL = Transition}] = {
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = Transition}]
    emp ++ (transitions.map(t => (t.sourcePC, t, t.targetPC)).seq)
  }

  /** Return a map from PC location to the set of variables that may be non-zero at that location. */
  protected lazy val nonZeroVariable: Map[String, Set[Variable]] = {

    val allVars = variables
    def default(s: String) = if (s == initPC) allVars else Set[Variable]()

    def transfer(nonZeros: Set[Variable], t: Transition) = {
      val az = t.assignedToZero(nonZeros)
      val anz = t.assignedToNonZero(nonZeros)
      val res = nonZeros -- az ++ anz
      Logger("integer.Program", LogDebug, "transfer: " + t.sourcePC + " -> " + t.targetPC + ": " + nonZeros + " -- " + az + " ++ " + anz)
      res
    }

    val map = cfa.aiFixpoint(
                    transfer,
                    ((a: Set[Variable], b: Set[Variable]) => a union b),
                    ((a: Set[Variable], b: Set[Variable]) => b subsetOf a),
                    default
    )
    Logger("integer.Program", LogDebug, "nonZeroVariable: " + map)
    map
  }

  protected lazy val nonZeroVariableButInit = nonZeroVariable - initPC

  protected def variableConflictGraph: DiGraph[GT.ULGT{type V = Variable}] = {
    val nonZeroMap = nonZeroVariableButInit
    //we can build a conflict graph where variables are in conflict iff they are live at the same time.
    val conflictsBase = (DiGraph.empty[GT.ULGT{type V = Variable}] /: variables)(_ + _)
    (conflictsBase /: nonZeroMap)( (acc, kv) => {
      val group = kv._2
      val edges = for (x <- group; y <- group if x != y) yield (x, (), y)
      acc ++ edges
    })
  }

  /** Return a list of groups of variables that may be merged safely.
   *  A safe merge means that the variables in a group are never non-zero at the same time.
   */
  protected def computeVariableMerge: Seq[Set[Variable]] = {
    val conflicts = variableConflictGraph
    val varToColor = conflicts.minimalColoring
    val colorToVar = varToColor.groupBy(_._2)
    val groups = colorToVar.values.map(_.map(_._1).toSet).toSeq
    assert(variables forall (v => groups exists (_ contains v)))
    groups
  }

  protected def computeVariableMergeApprox: Seq[Set[Variable]] = {
    val conflicts = variableConflictGraph
    def affinity(v1: Variable, v2: Variable): Int = {
      Misc.commonPrefix(v1.name, v2.name)
    }
    val nonZeroMap = nonZeroVariableButInit
    val largeClique = nonZeroMap.values.maxBy(_.size)
    conflicts.smallColoring(affinity, largeClique)
  }

  protected def reflow: Program = {
    //what we want to improve: constant and variable swapping.

    def node(pc: String, variable: Variable) = (pc,variable)

    //for each variables in each control state we create on node in the graph
    //connect them using TransitionHeuristics.variableFlow

    val allNodes = variables.toSeq.flatMap(v => pcs.map( node(_, v)))

    //var at the same loc are conlficting
    val samePC = for (pc <- pcs; v1 <- variables; v2 <- variables if v1 != v2) yield (node(pc,v1),node(pc,v2))
    val conflicts = DiGraph[GT.ULGT{type V = (String,Variable)}](samePC).addVertices(allNodes)

    //affinity: look at the flow
    //if there is an edge between the two vars: good
    //if that edge is on a cycle: better
    val edges = trs.flatMap(t => {
      val flows = TransitionHeuristics.variableFlow(t)
      val e = for ((x, ys) <- flows.iterator; y <- ys) yield (node(t.sourcePC, y), node(t.targetPC, x))
      val frame = (variables -- t.allVariables)
      val f = for (x <- frame.iterator) yield (node(t.sourcePC,x), node(t.targetPC,x))
      e ++ f
    })
    val flow = DiGraph[GT.ULGT{type V = (String,Variable)}](edges.seq).addVertices(allNodes)

    //there can be at most one var for each pc
    def trim(nodes: Set[(String,Variable)]): Set[(String,Variable)] = {
      nodes.groupBy(_._1).values.map(_.head).toSet
    }

    var scc = flow.SCC.map(trim)
    //now we must "grow" the scc as long as there are edges
    //  edges from/to a SCC and nothing from that pc
    //the nodes that are no in a SCC are not changed
    for ((a,b) <- edges.seq) {
       val sccA = scc.find(_ contains a).getOrElse(Set(a))
       val sccB = scc.find(_ contains b).getOrElse(Set(b))
       if (sccA != sccB) {
         //check if can be merged
         if ( (sccA.map(_._1) intersect sccB.map(_._1)).isEmpty ) {
           scc = scc.filterNot(cc => cc == sccA || cc == sccB) :+ (sccA ++ sccB)
         }
       }
    }

    //build the substitution
    val finalSCC = scc.zipWithIndex.map{ case (scc, i) => (scc, Variable("_SCC_" + i) ) }
    val pcToSubst: Map[String, Map[Variable, Variable]] = pcs.map( pc => {
      (pc, finalSCC.flatMap{ case (scc, v) => scc.find(_._1 == pc).map(_._2 -> v) }.toMap)
    }).toMap

    //for each transition apply the pre and post alpha
    val trs2 = trs.map( t => t.alphaPre(pcToSubst(t.sourcePC)).alphaPost(pcToSubst(t.targetPC)) )
    val p2 = new Program(initPC, trs2)
    p2//.reduceNumberOfVariables //TODO why deadlock ?
  }

  //take a group of variables and return the transitions modified s.t. only one variable is used for the group
  protected def mergeVariables(group: Set[Variable], trs: GenSeq[Transition]): GenSeq[Transition] = {
    Logger("integer.Program", LogDebug, "merging: " + group)
    if (group.size <= 1) {
      trs
    } else {
      val newVar = Variable("Merge_" + group.map(_.name).mkString("_"))
      trs.par.map( _.mergeVariables(group, newVar) )
    }
  }
  
  protected def compactPath = {
    val trs2 = cfa.simplePaths.flatMap( path => {
      Transition.compact(path.labels)
    })
    val p2 = new Program(initPC, trs2)
    Logger("integer.Program", LogInfo, "compactPath: #transitions before = " + transitions.size + ", after = " + p2.transitions.size)
    p2
  }

  //the unfold+fold might generate useless split+merge of some variable
  protected def lookForUselessSplitting = {
    //take a look at the var that gets split
    def split(s: Statement): Option[(Variable, List[Variable])] = s match {
      case Relation(lhs, rhs) =>
        val (lpos, lcst) = Expression.decompose(lhs)
        val (rpos, rcst) = Expression.decompose(rhs)
        if (lpos.size > 1 && rpos.size == 1) Some(rpos.head -> lpos)
        else None
      case _ => None
    }
    //take a look at the var that gets merge
    def merge(s: Statement): Option[(List[Variable], Variable)] = s match {
      case Relation(lhs, rhs) =>
        val (lpos, lcst) = Expression.decompose(lhs)
        val (rpos, rcst) = Expression.decompose(rhs)
        if(lpos.size == 1 && rpos.size > 1) Some(rpos -> lpos.head)
        else None
      case _ => None
    }
    //look at what changes
    def change(t: Transition): Set[Variable] = {
      val ids = t.updates flatMap {
        case Affect(v1, v2 @ Variable(_)) if v1 == v2 => Some(v1)
        case _ => None
      }
      t.updatedVars -- ids
    }
    //
    def lookForCandidates(trs: List[Transition],
                          candidates: List[(String, List[Variable])],
                          confirmed: List[(String, List[Variable], String)]
                         ):List[(String, List[Variable], String)] = trs match {
      case t :: ts =>
        val splitted: Seq[(Variable, List[Variable])] = t.updates flatMap split
        val merged: Seq[(List[Variable], Variable)] = t.updates flatMap merge
        val changed: Set[Variable] = change(t)
        val (confirmedCandidates, candidates2) = candidates.partition{ case (_, vars) =>
          val ms1 = MultiSet(vars:_*)
          merged.exists{ case (vars2, _) => 
            val ms2 = MultiSet(vars2:_*)
            val res = (ms1 -- ms2).isEmpty && (ms2 -- ms1).isEmpty //TODO: poor man's multiset equality
            //println("comparing: " + vars + " and " + vars2 + " -> " + res)
            //println("ms1: " + ms1 + ", ms2: " + ms2)
            //println("ms1 -- ms2: " + (ms1 -- ms2) + ", ms2 -- ms1: " + (ms2 -- ms1) )
            res
          }
        }
        //println("dropping because changed: " + candidates2.filterNot{ case (_, vars) => vars forall (v => !changed(v)) })
        val candidates3 = candidates2.filter{ case (_, vars) => vars forall (v => !changed(v)) }
        val newCandidates = splitted.map{ case (_, vars) => (t.sourcePC, vars) }
        val candidates4 = newCandidates.toList ++ candidates3
        val confirmed2 = confirmedCandidates.map{ case (src, vars) => (src, vars, t.targetPC) } ++ confirmed
        lookForCandidates(ts, candidates4, confirmed2)
      case Nil =>
        //println("at the end, still candidates: " + candidates.mkString(", "))
        confirmed
    }
    //
    def mergeConfirmed(trs: List[Transition],
                       confirmed: List[(String, List[Variable], String)],
                       inProgress: List[(List[Variable], String)],
                       acc: List[Transition]
                      ): List[Transition] = trs match {
      case t :: ts =>
        val (newInProgress, confirmed2) = confirmed.partition(_._1 == t.sourcePC)
        val (remains, lastMerge) = inProgress.partition(_._2 != t.targetPC)
        //splitting (newInProgress)
        //for newInProgress -> set the unused to 0
        val unusedVars = newInProgress.flatMap( _._2.tail.map(v => Affect(v, Constant(0))) )
        val t2 = (t /: newInProgress)( (tAcc, toMerge) => tAcc.mergePostVariablesDangerous(toMerge._2.toSet, toMerge._2.head) )
        //nothing changes (remains)
        val t3 = (t2 /: remains)( (tAcc, toMerge) => tAcc.mergeVariablesDangerous(toMerge._1.toSet, toMerge._1.head) )
        //merging (lastMerge)
        val t4 = (t3 /: lastMerge)( (tAcc, toMerge) => tAcc.mergePreVariablesDangerous(toMerge._1.toSet, toMerge._1.head) )
        //result
        val t5 = new Transition(t4.sourcePC, t4.targetPC, t4.guard, t4.updates ++ unusedVars, t4.comment)
        val inProgress2 = newInProgress.map{ case (_,a,b) => (a,b) } ++ remains
        mergeConfirmed(ts, confirmed2, inProgress2, t5::acc)
      case Nil =>
        assert(confirmed.isEmpty && inProgress.isEmpty)
        acc.reverse
    }
    //look for split+merge within simple paths.
    val trs2 = cfa.simplePaths.flatMap( path => {
      val trs = path.labels
      val uselessSplits = lookForCandidates(trs, Nil, Nil)
      for ( (src, lst, trgt) <- uselessSplits ) {
        Logger("integer.Program", LogInfo, "merging " + lst.mkString(", ") + " on the path from " + src + " to " + trgt )
      }
      mergeConfirmed(trs, uselessSplits, Nil, Nil)
    })
    //
    new Program(initPC, trs2)
  }

  def pruneAssumes = {
    val trs2 = trs.par.map(_.pruneAssume)
    new Program(initPC, trs2)
  }

  /** Try to remove guards and assume. */
  def pruneConditions = {
    //TODO compute bounds a the program level and then simplify the assumptions and the also the guards
    sys.error("TODO")
  }

  type Bounds = (Option[Int],Option[Int])
  type VarBounds = Map[Variable,Bounds]

  /** Compute upper and lower bound for variables at each PC location.
   *  This is a very coarse over-approximation of the actual bounds
   *  since it only looks at the guards and the assume statements.
   */
  def variablesBounds: Map[String,VarBounds] = {
    val vars = variables.toSeq 
    //a degenerate AI fixedpoint (join and cover goes into the opposite direction)
    def post(pre: VarBounds, t: Transition): VarBounds = t.variablesBounds(pre)
    def join(a: VarBounds, b: VarBounds): VarBounds = {
      a.map{ case (v, (aLow,aHigh)) =>
        val (bLow, bHigh) = b(v)
        val low = aLow.flatMap(v1 => bLow.map(v2 => math.min(v1,v2) ))
        val high = aHigh.flatMap(v1 => bHigh.map(v2 => math.max(v1,v2) ))
        assert(low.getOrElse(Int.MinValue) <= high.getOrElse(Int.MaxValue), "join of " + (aLow,aHigh) + " with " + (bLow, bHigh) )
        (v -> (low, high))
      }
    }
    //b and a are swapped since we have a decreasing fixedpoint (improve accuracy until it converges).
    def cover(b: VarBounds, a: VarBounds): Boolean = {
      vars.forall(v => {
        val (aLow, aHigh) = a(v)
        val (bLow, bHigh) = b(v)
        val low = aLow.isEmpty || bLow.map(_ >= aLow.get).getOrElse(false)
        val high = aHigh.isEmpty || bHigh.map(_ <= aHigh.get).getOrElse(false)
        (low && high)
      })
    }
    val default = Map[Variable,Bounds](vars.map(v => (v, (None, None))):_*)
    
    val map = cfa.aiFixpoint( post, join, cover, (_ => default))
    Logger("integer.Program", LogDebug, "variablesBounds: " + map)
    map
  }

  //TODO given a program: heuristically guess possible parts of the ranking function / transition predicates
  //What is the best way to do this
  //-> find the elementary cycles: for each cycle we should be able to find a simple candidate ranking fct
  //-> combining elementary cycles ...
  //what is a candidate ranking function ? -> a linear combination of terms + a lower bound
  //simple version of ranking fct: set of var (take the sum), the lower bounf is 0 (or any constant).
  def transitionPredicates: Iterable[Set[Variable]] = {
    val cycles = cfa.elementaryCycles.map(_.labels)
    val locToCycles = cycles.groupBy( c => c.head.sourcePC )
    val allCycles = locToCycles.values.flatMap( _.toSet.subsets ).filter( s => !s.isEmpty )
    //println("allCycles: " + allCycles.mkString("\n","\n",""))
    val allTrsPreds = allCycles.map( ts => Transition.transitionPredicates(ts.toSeq.flatten) )
    //val trsPreds = allTrsPreds.flatMap( candidates => if (candidates.isEmpty) None else Some(candidates.minBy(_.size))).toSet
    //trsPreds
    allTrsPreds.flatten.toSet
  }


}

/** A place where to put the heuritics analysis that we use for simplification */
object ProgramHeuritics {
  
  import TransitionHeuristics._

  /** A sink is a variable that only 'receives' and is unbounded. */
  def sinks(p: Program): Set[Variable] = {
    //works only for the non-init part
    assert(p.transitions forall (_.targetPC != p.initialPC))
    //restrict to variables that do not occurs as RHS
    val noInit = p.transitions.filter(_.sourcePC != p.initialPC)
    val neverRead = (p.variables /: noInit)((acc, t) => acc -- t.readVariables)
    val noRHS = (p.variables /: noInit)((acc, t) => acc -- t.readInUpdates)
    //let's get the bounds
    val bounds = p.variablesBounds
    val unboundedBelow = noRHS.filter(v => p.pcs.forall(bounds(_)(v)._1.isEmpty) )
    val unboundedAbove = noRHS.filter(v => p.pcs.forall(bounds(_)(v)._2.isEmpty) )
    val unboundedBoth = unboundedAbove intersect unboundedBelow
    //ignores the initialization transitions
    val changes = noInit.map(variablesChange)
    val belowSinks = unboundedBelow.filter( v => changes.forall( m => m.getOrElse(v, Fixed) == Fixed || m(v) == Decrease ) )
    val aboveSinks = unboundedAbove.filter( v => changes.forall( m => m.getOrElse(v, Fixed) == Fixed || m(v) == Increase ) )
    Logger("integer.Program", LogDebug, "neverRead = " + neverRead)
    Logger("integer.Program", LogDebug, "noRHS = " + noRHS)
    Logger("integer.Program", LogDebug, "sinks are: " + unboundedBoth + ", " + belowSinks + " and " + aboveSinks)
    neverRead ++ belowSinks ++ aboveSinks ++ unboundedBoth
  }

  def removeSinks(p: Program): Program = {
    //sinks in a loop: removing some var might create new sinks ...
    var toRemove = Set[Variable]()
    var p2 = p
    do {
      toRemove = sinks(p2)
      Logger("DBPTermination", LogInfo, "sinks: " + toRemove.mkString(", "))
      p2 = new Program(p2.initialPC, p2.transitions map (t => TransitionHeuristics.removeSinks(t, toRemove)))
    } while (!toRemove.isEmpty)
    p2
  }

  def simplifyMore(prog: Program): Program = {
    var p = prog
    for (i <- 0 until 2) {
      p = removeSinks(p.simplifyForTermination)
    }
    p
  }

  abstract class FlowKind
  case object ConstantFlow extends FlowKind
  case object TransferFlow extends FlowKind

  type FlowGraphGT = GT.ELGT{type V = Variable; type EL = FlowKind}
  type FlowGraph = EdgeLabeledDiGraph[FlowGraphGT]

  def flow(p: Program): FlowGraph = {
    var offsetEdges: GenSeq[(Variable, FlowKind, Variable)] = p.transitions.flatMap(t => {
      val (incr1, decr1) = constantOffset(t).view.partition{ case (k,v) => v > 0 }
      val incr = incr1.map(_._1)
      val decr = decr1.map(_._1)
      for (x <- decr; y <- incr) yield (x, ConstantFlow, y)
    })
    var transferEdges: GenSeq[(Variable, FlowKind, Variable)] = p.transitions.flatMap( t => {
      for ( (x, vs) <- variableFlow(t); y <- vs) yield (y, TransferFlow, x)
    })
    val edges: Iterable[(Variable, FlowKind, Variable)] = (offsetEdges ++ transferEdges).seq
    val edgesOnly = EdgeLabeledDiGraph[GT.ELGT{type V = Variable; type EL = FlowKind}](edges)
    val graph = edgesOnly.addVertices(p.variables)
    Logger("integer.ProgramHeuritics", LogInfo, graph.toGraphviz("flow"))
    graph
  }
  
  //use the flow to try merging variables.
  //The idea is to if it is possible to have a non-trivial embedding of the flow graph into itself.
  //Guess: the nodes that are not trivially mapped are good candidate for being merged.
  //TODO the current way is not really doing much. maybe we should relax the injectivity and do something like the folding of DB conf ?
  def counterMerging(p: Program): Iterable[Iterable[Variable]] = {
    import math.Ordering._
    val graph = flow(p)
    val morhisms = graph.subgraphIsomorphismAll(graph)
    val toMergePairs = morhisms.toIterable.view.flatMap( m => m.toIterable.filter{ case (k,v) => k != v } )
    val uf = new UnionFind[Variable]()
    for ( (a,b) <- toMergePairs ) uf.union(a, b)
    uf.getEqClasses.map(_._2)
  }
  
  def counterMergingMore(p: Program): Iterable[Iterable[Variable]] = {
    import math.Ordering._
    val graph = flow(p)
    val morphs = graph.morphisms[FlowGraphGT](graph, (_ : FlowGraphGT#V) => true, (_:graph.MorphInfo[FlowGraphGT]) => Nil)
    sys.error("TODO")

    /* example: folding loop from the DBConf
    def loop(accFolded: Self, accFolding: Morphism): (Self, Morphism) = {
      val iter = accFolded morphisms accFolded
      val changes = iter find ( m => {
        val used: Set[V] = (Set.empty[V] /: m)((acc, p) => acc + p._2)
        val redundant = accFolded.vertices &~ used
        !redundant.isEmpty
      })
      changes match {
        case Some(m) =>
          val redundant = (accFolded.vertices /: m.values)(_ - _)
          val accFolded2 = accFolded -- redundant
          val accFolding2: Morphism = accFolding.map[(V,V), Map[V,V]]{ case (a,b) => ( a, m.getOrElse(b,b) ) }
          loop(accFolded2, accFolding2)
        case None => (accFolded, accFolding)
      }
    }

    loop(this, vertices.map(v => (v,v)).toMap[V,V])    
    */
  }

  //TODO "from many places to few" abstraction

}
