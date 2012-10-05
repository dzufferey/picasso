package picasso.model.integer

import picasso.utils._
import picasso.graph._

class Transition(val sourcePC: String,
                 val targetPC: String,
                 val guard: Condition,
                 val updates: Seq[Statement],
                 val comment: String = "") extends picasso.math.Transition[State] {

  override def toString = {
    "Transition(" + sourcePC +
             ", " + targetPC +
             ", " + Condition.print(guard) +
             ", " + updates.map(Statement.print).mkString("{ ", "; ", "}") +
             ", \"" + comment + "\")"
  }
  
  def apply(s: State): Set[State] = {
    sys.error("TODO: for the moment the analysis of interger program is shipped to other tool")
  }

  def isDefinedAt(s: State): Boolean = {
    sourcePC == s.pc
  }

  def variables: Set[Variable] = {
    val updatesAll = (Set[Variable]() /: updates)(_ ++ Statement.getAllVariables(_))
    Condition.variables(guard) ++ updatesAll
  }

  /** the variables of this transition as a fixed sequence.
   *  (useful for pretty printing) */
  lazy val sequencedVariable: Seq[Variable] = variables.toSeq

  def guardVariables = Condition.variables(guard)

  def allVariables: Set[Variable] = {
    val updatesAll = (Set[Variable]() /: updates)(_ ++ Statement.getAllVariables(_))
    Condition.variables(guard) ++ updatesAll
  }

  lazy val sequencedAllVariables = allVariables.toSeq

  def updatedVars: Set[Variable] = {
    (Set[Variable]() /: updates)(_ ++ Statement.getUpdatedVars(_))
  }

  def readInUpdates: Set[Variable] = {
    (Set[Variable]() /: updates)(_ ++ Statement.getReadVariables(_))
  }
  
  def readVariables: Set[Variable] = {
    val inGuard = Condition.variables(guard)
    inGuard ++ readInUpdates
  }

  def alpha(subst: Map[Variable, Expression]) = {
    val guard2 = Condition.alpha(guard, subst)
    val updates2 = updates map ( Statement.alpha(_, subst) )
    new Transition(sourcePC, targetPC, guard2, updates2, comment)
  }

  def alphaPre(subst: Map[Variable, Expression]) = {
    val guard2 = Condition.alpha(guard, subst)
    val updates2 = updates map ( Statement.alphaPre(_, subst) )
    new Transition(sourcePC, targetPC, guard2, updates2, comment)
  }
  
  def alphaPost(subst: Map[Variable, Expression]) = {
    val updates2 = updates map ( Statement.alphaPost(_, subst) )
    new Transition(sourcePC, targetPC, guard, updates2, comment)
  }

}

/** A place where to put the heuritics analysis that we use for simplification */
object TransitionHeuristics {
  
/*
  def transitionPredicates(cycle: Seq[Transition]): Iterable[Set[Variable]] = {
    assert(!cycle.isEmpty && cycle.head.sourcePC == cycle.last.targetPC)
    //step 1: compact
    val compactable = cycle.zipWithIndex.map{ case (t,i) => new Transition("tp_"+i,"tp_"+(i+1), t.guard, t.updates, t.comment) }
    val compacted = Transition.compact(compactable)
    //take a subset of variables: look at the relation in which they apprears -> sum -> look at the constant term.
    //step 2: partition the variables (~ cone of influence)
    val graph = ProgramHeuristics.flow(compacted).undirect
    val maxPartition = graph.SCC(true)
    val uf = new UnionFind[Variable]()
    for ( (a,b,c) <- graph.edges if (b == ProgramHeuristics.TransferFlow) ) uf.union(a,c)
    val transfers = uf.getEqClasses.map(_._2.toSet) //parts connected by transfers (refinement of maxPartition)
    val partition = maxPartition.flatMap(p => {
        val containedTransfer = transfers filter (_ subsetOf p)
        val remaining = (p /: containedTransfer)(_ -- _)
        for(trans <- Misc.subSeqences(containedTransfer);
            rem <- remaining.subsets) yield trans.flatten.toSet ++ rem
    })
    //println("cycle: " + compacted.mkString(", "))
    //println("partitions: " + partition.mkString(", "))
    //step 3: compute the delta for each element of the partition
    def deltaT(part: Set[Variable], t: Transition): Option[Int] = {
      val relevant = t.updates.filter(s => Statement.getAllVariables(s) exists part)
      val (lhs, rhs, cst) = ((MultiSet[Variable](), MultiSet[Variable](), 0) /: relevant)( (acc, s) => (acc,s) match {
        case ((lhs, rhs, cst), Relation(_new, _old)) =>
          val (vn, cn) = Expression.decompose(_new)
          val (vo, co) = Expression.decompose(_old)
          (lhs ++ vn, rhs ++ vo, cst - cn.i + co.i)
        case _ => acc
      })
      //compare the lhs and the rhs to determine if we can handle that transition
      if ((lhs --* rhs.multiplicities).isEmpty &&
          (rhs --* lhs.multiplicities).isEmpty)
        Some(cst)
      else
        None
    }
    def delta(part: Set[Variable]): Option[Int] = {
      ((Some(0): Option[Int]) /: compacted)( (acc, t) => acc.flatMap(i => deltaT(part, t).map(_ + i)) )
    }

    val known = partition.flatMap( p => delta(p).map(i => i -> p) )
    val moreTP = if (Config.moreTPreds) known.groupBy(_._1) else (known.groupBy(_._1) - 0)
    val knownGrouped = moreTP.mapValues( lst => lst.map(_._2) )
    val deltaToPart = scala.collection.mutable.HashMap[Int, List[Set[Variable]]]( knownGrouped.toSeq : _* )
    //println("deltaToPart: " + deltaToPart.mkString(", "))
    //step 4: build candidates (combination of elt of the partition s.t. the sum of deltas is < 0)
    val seed = known.filter{ case (i,_) => i < 0 }
    val candidates = scala.collection.mutable.HashSet[Set[Variable]](seed.map(_._2): _*)
    def process(frontier: List[(Int, Set[Variable])]): Iterable[Set[Variable]] = frontier match {
      case (i, x) :: xs =>
        //println("confirmed: " + (i, x))
        // compute the successors ...
        val succ =  for ( (i2, lst) <- deltaToPart.iterator if i2 < -i;
                          x2 <- lst )
                    yield (i + i2, x ++ x2)
        val newCandidates = for ( (j,y) <- succ if !candidates(y) ) yield {
          //println("newCandidate: " + (j,y) )
          candidates += y
          val old: List[Set[Variable]] = deltaToPart.getOrElse(j, Nil)
          deltaToPart += (j -> (y :: old) )
          (j, y)
        }
        process(newCandidates ++: xs)
      case Nil => candidates
    }
    val res = process(seed.toList)
    Logger("integer.Transition", LogDebug, "transitionPredicates for:\n  " + cycle.mkString("\n  ") + "\n are\n" + res.mkString("\n"))
    res
  }
*/

}
