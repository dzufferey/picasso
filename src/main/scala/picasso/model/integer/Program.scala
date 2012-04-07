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
    Logger("integer.Program", LogDebug, "unsimplified program:\n" + this.printForQARMC)
    val p2 = this.propagateZeros
    Logger("integer.Program", LogDebug, "removing 0s:\n" + p2.printForQARMC)
    val p3 = p2.reduceNumberOfVariables
    Logger("integer.Program", LogDebug, "merging variables:\n" + p3.printForQARMC)
    p3
    //TODO for variables that are equals all the time -> keep only one
    //TODO remove strictly increasing 'sink' variables
    //TODO compact the transitions
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
    val equiv = computeEqualsVariable
    val substs = equiv.map{ case (pc, classes) =>
      val subst = classes.flatMap(x => x.map(y => (y -> x.head)) ).toMap
      (pc, subst)
    }
    val trs2 = transitions.map( t => {
      t.alphaPre(substs(t.sourcePC)).alphaPost(substs(t.targetPC))
    })
    new Program(initPC, trs2)
  }

  /** Return a map from PC location to the set of variables that may be non-zero at that location. */
  protected lazy val nonZeroVariable: Map[String, Set[Variable]] = {
    //TODO this is not correct (join is wrong)
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = Transition}]
    val cfa = emp ++ (transitions.map(t => (t.sourcePC, t, t.targetPC)).seq)

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
      (v1.name zip v2.name).takeWhile{ case (a,b) => a == b}.length
    }
    val largeClique = nonZeroMap.values.maxBy(_.size)
    conflicts.smallColoring(affinity, largeClique)
  }

  //take a group of variables and return the transitions modified s.t. only one variable is used for the group
  protected def mergeVariables(group: Set[Variable], trs: GenSeq[Transition]): GenSeq[Transition] = {
    Logger("integer.AST", LogDebug, "merging: " + group)
    if (group.size <= 1) {
      trs
    } else {
      val newVar = Variable("Merge_" + group.map(_.name).mkString("_"))
      trs.map( _.mergeVariables(group, newVar, nonZeroVariable) )
    }
  }
  
  protected def computeEqualsVariable: Map[String, Set[Set[Variable]]] = {
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = Transition}]
    val cfa = emp ++ (transitions.map(t => (t.sourcePC, t, t.targetPC)).seq)

    //the AI elements are sets of equivalence class (set of variables)

    def default(pc: String) = Set(nonZeroVariable(pc)) //TODO all the other are difference ?

    def transfer(eqClasses: Set[Set[Variable]], t: Transition) = {
      t.equivalenceClasses(eqClasses)
    }

    def join(a: Set[Set[Variable]], b: Set[Set[Variable]]): Set[Set[Variable]] = {
      //the join is a refinement of a and b
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

}
