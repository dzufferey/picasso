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

  def variables: Set[Variable] = {
    trs.aggregate(Set[Variable]())(_ ++ _.variables, _ ++ _)
  }

  def printForARMC = {
    val str = new java.io.StringWriter()
    val writer = new java.io.BufferedWriter(str)
    ARMCPrinter(writer, this)
    writer.close
    str.toString
  }
  
  def printForQARMC = {
    val str = new java.io.StringWriter()
    val writer = new java.io.BufferedWriter(str)
    QARMCPrinter(writer, this)
    writer.close
    str.toString
  }
  
  def printForT2 = {
    sys.error("TODO")
  }

  /** try to simplify the program while preserving (non)termination. */
  def simplifyForTermination = {
    //repeat a few time ...
    var p = this
    for (i <- 0 until 3) {
      p = p.simplifyForTermination1
    }
    p
  }
  
  def simplifyForTermination1 = {
    Logger("integer.Program", LogDebug, "unsimplified program:\n" + this.printForQARMC)
    Logger("integer.Program", LogInfo, "propagating zeros.")
    val p2 = this.propagateZeros
    Logger("integer.Program", LogDebug, "removing 0s:\n" + p2.printForQARMC)
    //Logger("integer.Program", LogInfo, "removing equal variables.")
    //val p3 = p2.removeEqualsVariables
    //Logger("integer.Program", LogDebug, "equal variables:\n" + p3.printForQARMC)
    Logger("integer.Program", LogInfo, "merging variables.")
    val p4 = p2.reduceNumberOfVariables
    Logger("integer.Program", LogDebug, "merging variables:\n" + p4.printForQARMC)
    Logger("integer.Program", LogInfo, "compacting transitions.")
    val p5 = p4.compactPath
    Logger("integer.Program", LogDebug, "compacting transitions:\n" + p5.printForQARMC)
    Logger("integer.Program", LogInfo, "removing useless split.")
    val p6 = p5.lookForUselessSplitting
    Logger("integer.Program", LogDebug, "looking for useless splitting:\n" + p6.printForQARMC)
    Logger("integer.Program", LogInfo, "pruning Assume.")
    val p7 = p6.pruneAssumes
    Logger("integer.Program", LogDebug, "assumed pruned:\n" + p7.printForQARMC)
    p7
    //TODO remove (strictly increasing) 'sink' variables
    //TODO transition in sequence that operates on disjoint set of variable might be merged (if the control flow is linear)
  }

  def propagateZeros = {
    val allVars = variables
    val nonZeros = nonZeroVariable
    val zeros = nonZeros.map{ case (k, nz) => (k, allVars -- nz) }
    val trs2 = transitions.map(t => {
      val preSubst = zeros(t.sourcePC).map( _ -> Constant(0) ).toMap
      //val postSubst = zeros(t.targetPC).map( _ -> Constant(0) ).toMap
      t.alphaPre(preSubst)/*.alphaPost(postSubst)*/.leaner
    })
    new Program(initPC, trs2)
  }

  def reduceNumberOfVariables = {
    //if two variables are not live at the same moment, we can merge them!
    val groups = computeVariableMergeApprox
    val trs2 = (transitions /: groups)( (trs, grp) => mergeVariables(grp, trs) )
    val p2 = new Program(initPC, trs2)
    Logger("integer.Program", LogInfo, "reduceNumberOfVariables: #variables before = " + variables.size + ", after = " + p2.variables.size)
    p2.renameVariables
  }

  /** create shorter names for the variables */
  def renameVariables = {
    val namer = new Namer
    val subst = variables.map(v => (v, Variable(namer("X")) ) ).toMap
    val trs2 = transitions.map(_.alpha(subst))
    new Program(initPC, trs2)
  }

  /** If two variables are always equal, we can keep only one */
  def removeEqualsVariables = {
    val eqClasses = computeEqualsVariable
    def join(a: Set[Set[Variable]], b: Set[Set[Variable]]): Set[Set[Variable]] = {
      val product = for (ec1 <- a; ec2 <- b) yield ec1 intersect ec2
      product.filterNot(_.isEmpty)
    }
    val alwaysEqual = (eqClasses - initPC).values.reduceLeft(join)
    def classesToSubst(classes: Set[Set[Variable]]) = classes.toSeq.flatMap( set => set.map(x => (x -> set.head)) ).toMap
    //val substMap = eqClasses.map{ case (k, v) => (k -> classesToSubst(v))}
    val subst = classesToSubst(alwaysEqual).filter{ case (k,v) => k != v }
    Logger("integer.Program", LogDebug, "removeEqualsVariables is merging: " + subst)
    val trs2 = transitions.map(t => t.alpha(subst).leaner)
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
      //Logger("integer.Program", LogDebug, "transfer: " + t.sourcePC + " -> " + t.targetPC + ": " + nonZeros + " -- " + az + " ++ " + anz)
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

  /** Return a list of groups of variables that may be merged safely.
   *  A safe merge means that the variables in a group are never non-zero at the same time.
   */
  protected def computeVariableMerge: Seq[Set[Variable]] = {
    val nonZeroMap = nonZeroVariableButInit
    //we can build a conflict graph where variables are in conflict iff they are live at the same time.
    val conflictsBase = (DiGraph.empty[GT.ULGT{type V = Variable}] /: variables)(_ + _)
    val conflicts = (conflictsBase /: nonZeroMap)( (acc, kv) => {
      val group = kv._2
      val edges = for (x <- group; y <- group if x != y) yield (x, (), y)
      acc ++ edges
    })
    val varToColor = conflicts.minimalColoring
    val colorToVar = varToColor.groupBy(_._2)
    val groups = colorToVar.values.map(_.map(_._1).toSet).toSeq
    assert(variables forall (v => groups exists (_ contains v)))
    groups
  }

  protected def computeVariableMergeApprox: Seq[Set[Variable]] = {
    val nonZeroMap = nonZeroVariableButInit
    //we can build a conflict graph where variables are in conflict iff they are live at the same time.
    val conflictsBase = (DiGraph.empty[GT.ULGT{type V = Variable}] /: variables)(_ + _)
    val conflicts = (conflictsBase /: nonZeroMap)( (acc, kv) => {
      val group = kv._2
      val edges = for (x <- group; y <- group if x != y) yield (x, (), y)
      acc ++ edges
    })
    def affinity(v1: Variable, v2: Variable): Int = {
      Misc.commonPrefix(v1.name, v2.name)
    }
    val largeClique = nonZeroMap.values.maxBy(_.size)
    conflicts.smallColoring(affinity, largeClique)
  }

  //take a group of variables and return the transitions modified s.t. only one variable is used for the group
  protected def mergeVariables(group: Set[Variable], trs: GenSeq[Transition]): GenSeq[Transition] = {
    Logger("integer.Program", LogDebug, "merging: " + group)
    if (group.size <= 1) {
      trs
    } else {
      val newVar = Variable("Merge_" + group.map(_.name).mkString("_"))
      trs.map( _.mergeVariables(group, newVar) )
    }
  }
  
  protected def computeEqualsVariable: Map[String, Set[Set[Variable]]] = {
    //TODO this approach does not work
    //need to differentiate bewteen different from has not information
    //otherwise, the back edges prevent the equality information from propagating

    //the AI elements are sets of equivalence class (set of variables)

    def default(pc: String): Set[Set[Variable]] = {
      val allVars = variables
      val zeros = allVars -- nonZeroVariable(pc)
      if (pc == initPC) {
        val rest = nonZeroVariable(pc)
        (Set(zeros) /: rest)( (acc, v) => acc + Set(v) ).filterNot(_.isEmpty)
      } else {
        Set()
      }
    }

    def transfer(eqClasses: Set[Set[Variable]], t: Transition) = {
      t.equivalenceClasses(eqClasses, nonZeroVariable)
    }

    //TODO the join should be more complex since the equivalence classes do not contains all the nodes ...
    def join(a: Set[Set[Variable]], b: Set[Set[Variable]]): Set[Set[Variable]] = {
      //the join is a refinement of a and b
      //println("join of " + a + " and " + b)
      val product = for (ec1 <- a; ec2 <- b) yield ec1 intersect ec2
      product.filterNot(_.isEmpty)
    }

    def cover(a: Set[Set[Variable]], b: Set[Set[Variable]]): Boolean = {
      //b is a refinement of a, i.e. there is more info in a than in b
      b forall (x => a exists (y => x subsetOf y))
    }

    val map = cfa.aiFixpoint( transfer, join, cover, default)
    Logger("integer.Program", LogDebug, "equivalenceClasses: " + map)
    map
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
        val (lpos, lneg, lcst) = Expression.decompose(lhs)
        val (rpos, rneg, rcst) = Expression.decompose(rhs)
        if (lpos.size > 1 && lneg.isEmpty && rpos.size == 1 && rneg.isEmpty) Some(rpos.head -> lpos)
        else None
      case _ => None
    }
    //take a look at the var that gets merge
    def merge(s: Statement): Option[(List[Variable], Variable)] = s match {
      case Relation(lhs, rhs) =>
        val (lpos, lneg, lcst) = Expression.decompose(lhs)
        val (rpos, rneg, rcst) = Expression.decompose(rhs)
        if(lpos.size == 1 && lneg.isEmpty && rneg.isEmpty && rpos.size > 1) Some(rpos -> lpos.head)
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
    val trs2 = transitions.map(_.pruneAssume)
    new Program(initPC, trs2)
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
