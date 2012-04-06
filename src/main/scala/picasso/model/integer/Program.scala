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
    val trs2 = transitions.map(_.leaner)
    val p2 = new Program(initPC, trs2)
    p2.reduceNumberOfVariables
    //TODO compact the transitions
    //TODO transition in sequence that operates on disjoint set of variable might be merged (if the control flow is linear)
  }

  def reduceNumberOfVariables = {
    //if two variables are not live at the same moment, we can merge them!
    val groups = computeVariableMerge
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

  /** Return a map from PC location to the set of variables that may be non-zero at that location. */
  protected lazy val nonZeroVariable: Map[String, Set[Variable]] = {
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = Transition}]
    val cfa = emp ++ (transitions.map(t => (t.sourcePC, t, t.targetPC)).seq)

    val allVars = variables
    def default(s: String) = if (s == initPC) allVars else Set[Variable]()

    //TODO improve the precision: if something that is 0 is transfered then that thing is also 0
    def transfer(nonZeros: Set[Variable], t: Transition) = {
      val az = t.assignedToZero
      val anz = t.assignedToNonZero
      val res = nonZeros -- az ++ anz
      //Logger("integer.Program", LogDebug, "transfer: " + t.sourcePC + " -> " + t.targetPC + ": " + nonZeros + " -- " + az + " ++ " + anz)
      res
    }

    val map = cfa.aiFixpoint(
                    transfer,
                    ((a: Set[Variable], b: Set[Variable]) => a ++ b),
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
    val conflicts = (DiGraph.empty[GT.ULGT{type V = Variable}] /: nonZeroMap)( (acc, kv) => {
      val group = kv._2
      val edges = for (x <- group; y <- group if x != y) yield (x, (), y)
      acc ++ edges
    })
    //Then we need to find a minimal coloring of the graph
    //Since the problem is hard it makes sense to use a greedy algorithm with heuristics rather than finding an optimal coloring.
    //TODO look at http://shah.freeshell.org/graphcoloring/ or http://code.google.com/p/graphcol/ for some good heuristic
    //The idea of the greedy algorithm is to associate the first available color to a node.
    //To add the heuristics, we should rank the available colors according to some distance.
    //In this case two nodes are close if they share a long prefix.
    //another idea for the heuristic is to look at which variable flow into which one.
    def affinity(v1: Variable, v2: Variable): Int = {
      (v1.name zip v2.name).takeWhile{ case (a,b) => a == b}.length
    }
    val allVars = variables
    val averageAffinity = {
      var total = 0
      var sum = 0
      val edges = for (x <- allVars; y <- allVars if x != y)  {
        total += 1
        sum += affinity(x, y)
      }
      if (total > 0) sum.toDouble / total.toDouble
      else 0
    }
    //greedy coloring:
    val varToColor = scala.collection.mutable.HashMap[Variable, Int]()
    val colorToVar = scala.collection.mutable.HashMap[Int, List[Variable]]()
    var newColor = 0
    //seeding the coloring
    val largeClique = nonZeroMap.values.maxBy(_.size)
    for (v <- largeClique) {
      varToColor += (v -> newColor)
      colorToVar += (newColor -> (v :: colorToVar.getOrElse(newColor, Nil)))
      newColor += 1
    }
    //now coloring the rest
    for (v <- (allVars -- largeClique)) {
      val conflicting: Set[Int] = conflicts(v).flatMap(varToColor get _)
      val available = (0 until newColor).filterNot( conflicting contains _ )
      if (available.isEmpty) {
        varToColor += (v -> newColor)
        colorToVar += (newColor -> (v :: colorToVar.getOrElse(newColor, Nil)))
        newColor += 1
      } else {
        val scored = available.map(c => {
          val others = colorToVar(c)
          (c, others.map(v2 => affinity(v, v2)).max)
        })
        val (c, score) = scored.maxBy(_._2)
        if(score >= averageAffinity) {
          varToColor += (v -> c)
          colorToVar += (c -> (v :: colorToVar.getOrElse(c, Nil)))
        } else {
          varToColor += (v -> newColor)
          colorToVar += (newColor -> (v :: colorToVar.getOrElse(newColor, Nil)))
          newColor += 1
        }
      }
    }
    //return the coloring
    val groups = colorToVar.values.map(_.toSet).toSeq
    assert(variables forall (v => groups exists (_ contains v)))
    groups
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

}
