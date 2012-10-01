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
    val updatesTransient = (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
    Condition.variables(guard) ++ updatesAll -- updatesTransient
  }

  /** the variables of this transition as a fixed sequence.
   *  (useful for pretty printing) */
  lazy val sequencedVariable: Seq[Variable] = variables.toSeq

  def guardVariables = Condition.variables(guard)

  def transientVariables: Set[Variable] = {
    (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
  }

  def allVariables: Set[Variable] = {
    val updatesAll = (Set[Variable]() /: updates)(_ ++ Statement.getAllVariables(_))
    Condition.variables(guard) ++ updatesAll
  }

  lazy val sequencedAllVariables = allVariables.toSeq

  def updatedVars: Set[Variable] = {
    val updated = (Set[Variable]() /: updates)(_ ++ Statement.getUpdatedVars(_))
    val transient = (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
    updated -- transient
  }

  def readInUpdates: Set[Variable] = {
    val read = (Set[Variable]() /: updates)(_ ++ Statement.getReadVariables(_))
    val transient = (Set[Variable]() /: updates)(_ ++ Statement.getTransientVariables(_))
    read -- transient
  }
  
  def readVariables: Set[Variable] = {
    val inGuard = Condition.variables(guard)
    inGuard ++ readInUpdates
  }

  /** Extract the simples updates that occurs in the transitions.
   *  More complex updates are ignored */
  lazy val simpleUpdates: Map[Variable, (List[Variable], Constant)] = {
    updates.flatMap{
      case Affect(v, expr) => Some(v -> Expression.decompose(expr))
      case _ => None
    }.toMap
  }
    
  //is not exact but a superset
  //this assumes the variables are positive
  def assignedToNonZero(preNonZero: Set[Variable]): Set[Variable] = {
    val nonZeros = updates.flatMap{
      case Relation(lhs, rhs) =>
        val (pos, cst) = Expression.decompose(rhs)
        val pos2 = pos.filter(v => preNonZero(v) || updates.exists(_ == Transient(v)))
        if (pos2.isEmpty && cst.i == 0) Set()
        else Expression.variables(lhs)
      case _ => None
    }
    val nz = nonZeros.toSet
    assert(nz subsetOf updatedVars)//check that no transient has been caught
    nz
  }
  
  //is not exact but a subset
  //this assumes the variables are positive
  def assignedToZero(preNonZero: Set[Variable]): Set[Variable] = {
    simpleUpdates.view.flatMap{
      case (v, (vars, cst)) =>
        val vars2 = vars.filter(preNonZero)
        if (vars2.isEmpty && cst.i == 0) Some(v)
        else None
    }.toSet
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

  //TODO can we have a method to eliminate the transient vars ?
  //as a special case of quantifier elimination ?
  //transient vars are used to preserve some difference between primed and unprimed

  /** Remove unneeded/unchanged variables */
  def leaner: Transition = {
    val guard2 = Condition.simplify(guard)
    val updates2 = updates.map(Statement.simplify)
    val (changing, notChanging) = updates2.partition{
      case Relation(Variable(v1), Variable(v2)) => v1 != v2
      case _ => true
    }
    //the variables that stays constant
    val notChangingVars = notChanging.map{case Affect(v1, v2) => v1}.toSet
    //the variable needed for some other transition
    val neededForGuard = Condition.variables(guard2)
    val transient = transientVariables
    val neededForChanging = (Set[Variable]() /: changing)(_ ++ Statement.getAllVariables(_))
    val toRemove = notChangingVars -- neededForGuard -- transient -- neededForChanging
    val updates3 = updates2.filter{ case Affect(v1, v2) => v1 != v2 || !toRemove(v1) case Skip => false case _ => true }
    val t2 = new Transition(sourcePC, targetPC, guard2, updates3, comment)
    assert((t2.variables intersect toRemove).isEmpty)
    t2
  }

  protected def mergeInExpression(group: Set[Variable], newVar: Variable, e: Expression): Expression = {
    val (pos, cst) = Expression.decompose(e)
    if (pos.exists(group contains _)) {
      val pos2 = newVar :: pos.filterNot(group contains _)
      Expression.recompose(pos2, cst)
    } else {
      e
    }
  }

  protected def mergeInCondition(group: Set[Variable], newVar: Variable, c: Condition): Condition = c match {
    case Eq(l,r) => Eq(mergeInExpression(group, newVar, l), mergeInExpression(group, newVar, r))
    case Lt(l,r) => Lt(mergeInExpression(group, newVar, l), mergeInExpression(group, newVar, r))
    case Leq(l,r) => Leq(mergeInExpression(group, newVar, l), mergeInExpression(group, newVar, r))
    case And(l,r) => And(mergeInCondition(group, newVar, l), mergeInCondition(group, newVar, r))
    case Or(l,r) => Or(mergeInCondition(group, newVar, l), mergeInCondition(group, newVar, r))
    case Not(c) => Not(mergeInCondition(group, newVar, c))
    case l @ Literal(_) => l
  }
  

  /** Return a transitions s.t. only one variable is used for the group 
   *  This method assumes that only one variable of the group can be nonZeros at the time (except for the initial state).
   */
  def mergeVariables(group: Set[Variable], newVar: Variable): Transition = {
    //need to look which var is assigned to 0:
    //val anz = assignedToNonZero(allVariables).filter(group contains _)
    //assert(anz.size <= 1, "mergeVariables: " + group + " -> " + this) TODO this is not true for the init transitions
    //TODO there should be some more sanity checks ? / make sanity check faster

    //TODO may return wrong results when x_1 := x_4, x_4 := x_1 - 1, x_10 := x_10 (merge x_4,x_10)
    //works when x_1 := x_1, x_4 := x_4 - 1, x_10 := x_10 (merge x_4,x_10)

    /*
    assert( {
        if ((allVariables intersect group).size > 1) {
          updates.forall(s =>
            if (Statement.getReadVariables(s).exists(group)) Statement.getUpdatedVars(s).exists(group)
            else true)
        } else true},
      "mergeVariables: " + group + " -> " + this
    )
    */

    //println("XXX tr: " + this)
    //println("XXX group: " + group)
    //println("XXX newVar: " + newVar)
    //println("XXX anz: " + anz)

    val nonGroupIndex = (for (i <- 0 until sequencedAllVariables.length if !group(sequencedAllVariables(i)) ) yield i).toSeq
    val groupIndex = (for (i <- 0 until sequencedAllVariables.length if group(sequencedAllVariables(i)) ) yield i).toSeq
    val varToIdx = sequencedAllVariables.view.zipWithIndex.toMap

    var seenNew = Set[Variable]()
    var seenOld = Set[Variable]()
    val toSumNew = Array.ofDim[Int](sequencedAllVariables.length)
    val toSumOld = Array.ofDim[Int](sequencedAllVariables.length)
    var toSumCst = 0 //cst is on the old side

    def processStmt(s: Statement): Statement = s match {
      case Relation(_new, _old) =>
        if (Expression.variables(_new).exists(group contains _)) {
          val (newV, newC) = Expression.decomposeVector(_new, varToIdx)
          val (oldV, oldC) = Expression.decomposeVector(_old, varToIdx)
          //check if this is something we can handle
          for (i <- groupIndex) {
            if (newV(i) == 1) {
              assert(!seenNew(sequencedAllVariables(i)), "TODO more complex sum: " + s)
              seenNew += sequencedAllVariables(i)
            } else if (newV(i) >= 1) {
              assert(false, "TODO more complex sum: " + s)
            }
            if (oldV(i) == 1) {
              assert(!seenOld(sequencedAllVariables(i)), "TODO more complex sum: " + s)
              seenOld += sequencedAllVariables(i)
            } else if (oldV(i) >= 1) {
              assert(false, "TODO more complex sum: " + s)
            }
          }
          //simple case: not more than once
          for (idx <- nonGroupIndex) {
            toSumNew(idx) += newV(idx)
            toSumOld(idx) += oldV(idx)
          }
          toSumCst += (oldC - newC)
          Skip //return nothing since the new constraint will be generated later
        } else if (Expression.variables(_old).exists(group contains _)) {
          //merge the rhs
          Relation(_new, mergeInExpression(group, newVar, _old))
        } else {
          s
        }
      
      case Assume(cond) =>
        Statement.simplify(Assume(mergeInCondition(group, newVar, cond)))
      
      case Variance(_new, _old, greater, strict) =>
        if (group(_new) || group(_old)) {
          Logger("integer.Transition", LogWarning, "mergeVariables changing: " + s + ", dropping the constraint")
          Skip
        } else {
          s
        }
      
      case Skip | Transient(_) =>
        s
    }

    val updates2 = updates.map(processStmt)

    val updates3 =
      if(!seenNew.isEmpty) {
        val new1 = Expression.recomposeVector(toSumNew, 0, sequencedAllVariables)
        val old1 = Expression.recomposeVector(toSumOld, toSumCst, sequencedAllVariables)
        val new2 = if (seenNew.isEmpty) new1 else Plus(newVar, new1)
        val old2 = if (seenOld.isEmpty) old1 else Plus(newVar, old1)
        Relation(new2, old2) +: updates2
      } else {
        updates2
      }
    
    val guard2 = mergeInCondition(group, newVar, guard)
    
    val t2 = new Transition(sourcePC, targetPC, guard2, updates3, comment)
    
    //println("mergeVariables: " + group + " -> " + newVar)
    //println("old: " + this)
    //println("new: " + t2)

    t2.leaner

  }
  
  //HACK: works only in the context of lookForUselessSplitting
  def mergePreVariablesDangerous(group: Set[Variable], newVar: Variable): Transition = {
    val guard2 = mergeInCondition(group, newVar, guard)
    val updates2 = updates.map( s => s match {
      case Relation(x, y) => Relation(x, mergeInExpression(group, newVar, y))
      case vr @ Variance(v1, v2, g, s) => if (group(v2)) Variance(v1, newVar, g, s) else vr
      case other => other
    })
    //println("mergePreVariablesDangerous " + group + ", " + newVar +
    //        updates.mkString("\n","\n","\n---------") + updates2.mkString("\n","\n","\n========="))
    val t2 = new Transition(sourcePC, targetPC, guard2, updates2, comment)
    t2.leaner
  }

  //HACK: works only in the context of lookForUselessSplitting
  def mergePostVariablesDangerous(group: Set[Variable], newVar: Variable): Transition = {
    val updates2 = updates.map( s => s match {
      case Relation(x, y) => Relation(mergeInExpression(group, newVar, x), y)
      case Assume(c) => Assume(mergeInCondition(group, newVar, c))
      case vr @ Variance(v1, v2, g, s) => if (group(v1)) Variance(newVar, v2, g, s) else vr
      case other => other
    })
    //println("mergePostVariablesDangerous " + group + ", " + newVar +
    //        updates.mkString("\n","\n","\n---------") + updates2.mkString("\n","\n","\n========="))
    val t2 = new Transition(sourcePC, targetPC, guard, updates2, comment)
    t2.leaner
  }
  
  //HACK: works only in the context of lookForUselessSplitting
  def mergeVariablesDangerous(group: Set[Variable], newVar: Variable): Transition = {
    mergePreVariablesDangerous(group, newVar).mergePostVariablesDangerous(group, newVar)
  }


  //TODO unify the bounds computation

  protected def mergeBounds(m1: Map[Variable, Int], m2: Map[Variable, Int], minOrMax: (Int, Int) => Int): Map[Variable, Int] = {
    val keys = m1.keySet ++ m2.keySet
    (Map[Variable,Int]() /: keys)( (acc, v) => {
      val bound: Int = (m1.get(v), m2.get(v)) match {
        case (Some(b1), Some(b2)) => minOrMax(b1, b2)
        case (Some(b), None) => b
        case (None, Some(b)) => b
        case (None, None) => Logger.logAndThrow("integer.Transition", LogError, "mergeBounds -> no bounds")
      }
      acc + (v -> bound)
    })
  }

  protected def getTransientLowerBounds: Map[Variable, Int] = {
    val tr = transientVariables
    (Map[Variable, Int]() /: updates)( (acc, s) => s match {
      case Assume(c) =>
        val lb = Condition.getLowerBounds(c).filterKeys(transientVariables)
        mergeBounds(acc, lb, math.max)
      case _ => acc
    })
  }
  
  //lower and upper bounds refer to the pre state/guards
  protected def getPostLowerBounds(lowerBounds: Map[Variable, Int], upperBounds: Map[Variable, Int]) = {
    (Map[Variable, Int]() /: updates)( (acc, s) => s match {
      case Relation(e1, e2) =>
        val (p1, c1) = Expression.decompose(e1)
        if (p1.size != 1) {
          acc //cannot say anything
        } else {
          val (p2, c2) = Expression.decompose(e2)
          if (p2.forall(lowerBounds contains _)) {
            val lb2 = (0 /: p2.map(lowerBounds))(_ + _) - c1.i + c2.i
            val v1 = p1.head
            if (acc contains v1) acc + (v1 -> math.max(acc(v1), lb2))
            else acc + (v1 -> lb2)
          } else {
            acc
          }
        }
      case Variance(v1, v2, g, s) if g && lowerBounds.contains(v2) =>
        val lb2 = if (s) lowerBounds(v2) + 1 else lowerBounds(v2)
        if (acc contains v1) acc + (v1 -> math.max(acc(v1), lb2))
        else acc + (v1 -> lb2)
      case _ => acc
    })
  }
  
  protected def getTransientUpperBounds: Map[Variable, Int] = {
    val tr = transientVariables
    (Map[Variable, Int]() /: updates)( (acc, s) => s match {
      case Assume(c) =>
        val ub = Condition.getUpperBounds(c).filterKeys(transientVariables)
        mergeBounds(acc, ub, math.min)
      case _ => acc
    })
  }

  protected def getPostUpperBounds(lowerBounds: Map[Variable, Int], upperBounds: Map[Variable, Int]) = {
    (Map[Variable, Int]() /: updates)( (acc, s) => s match {
      case Relation(e1, e2) =>
        val (p1, c1) = Expression.decompose(e1)
        if (p1.size != 1) {
          acc //cannot say anything
        } else {
          val (p2, c2) = Expression.decompose(e2)
          if (p2.forall(upperBounds contains _)) {
            val lb2 = (0 /: p2.map(upperBounds))(_ + _) - c1.i + c2.i
            val v1 = p1.head
            if (acc contains v1) acc + (v1 -> math.min(acc(v1), lb2))
            else acc + (v1 -> lb2)
          } else {
            acc
          }
        }
      case Variance(v1, v2, g, s) if !g && upperBounds.contains(v2) =>
        val lb2 = if (s) upperBounds(v2) - 1 else upperBounds(v2)
        if (acc contains v1) acc + (v1 -> math.min(acc(v1), lb2))
        else acc + (v1 -> lb2)
      case _ => acc
    })
  }

  def pruneAssume = {
    //guards
    val lowerBounds = Condition.getLowerBounds(guard) ++ getTransientLowerBounds
    val upperBounds = Condition.getUpperBounds(guard) ++ getTransientUpperBounds
    //updates
    val postLowerBounds = getPostLowerBounds(lowerBounds, upperBounds)
    val postUpperBounds = getPostUpperBounds(lowerBounds, upperBounds)
    //prune
    def canProveExpr(e1: Expression, e2: Expression, strict: Boolean) = {
      //upper bound of e1 is less than lowerbound of e2
      val (p1, c1) = Expression.decompose(e1)
      val (p2, c2) = Expression.decompose(e2)
      try {
        val upper1 = (0 /: p1)(_ + postUpperBounds(_)) + c1.i
        val lower2 = (0 /: p2)(_ + postLowerBounds(_)) + c2.i
        if (strict) upper1 < lower2 else upper1 <= lower2
      } catch {
        case _ => false
      }
    }
    def canProve(c: Condition): Boolean = c match {
      case Eq(e1, e2) => canProve(Leq(e1, e2)) && canProve(Leq(e2, e1))
      case Leq(e1, e2) => canProveExpr(e1, e2, false)
      case Lt(e1, e2) => canProveExpr(e1, e2, true)
      case And(c1, c2) => canProve(c1) && canProve(c2)
      case Or(c1, c2) => canProve(c1) || canProve(c2)
      case _ => false
    }
    val updates2 = updates.map( s => s match {
      case a @ Assume(c) if canProve(c) =>
        Logger("integer.Transition", LogInfo, "pruneAssume could prove: " + a + ", dropping it safely")
        Skip
      case other => other
    })
    new Transition(sourcePC, targetPC, guard, updates2, comment)
  }
  
  def variablesBounds(pre: Map[Variable,(Option[Int],Option[Int])]): Map[Variable,(Option[Int],Option[Int])] = {

    //the pre bound is needed: in the case of increasing variables we keep the lower bound, same for upper
    def merge(guardBounds: Map[Variable, Int],
              select: Pair[Option[Int],Option[Int]] => Option[Int],
              minOrMax: (Int, Int) => Int): Map[Variable, Int] = {
      val merged = pre.flatMap{
        case (v, lowHigh) =>
          val preDefined: Option[Int] = select(lowHigh).map(b => minOrMax(b, guardBounds.getOrElse(v, b)))
          val guardDefined: Option[Int] = preDefined.orElse(guardBounds.get(v))
          guardDefined.map(b => (v, b))
      }
      merged.toMap
    }

    //guards
    val lowerBounds = Condition.getLowerBounds(guard) ++ getTransientLowerBounds
    val upperBounds = Condition.getUpperBounds(guard) ++ getTransientUpperBounds
    //merged
    val lowerBoundsMerged = merge(lowerBounds, _._1, math.max)
    val upperBoundsMerged = merge(upperBounds, _._2, math.min)
    //updates
    val postLowerBounds = getPostLowerBounds(lowerBoundsMerged, upperBoundsMerged)
    val postUpperBounds = getPostUpperBounds(lowerBoundsMerged, upperBoundsMerged)
    //frame
    val frame = pre -- updatedVars

    val res = pre.map{ case (v,_) => (v -> (postLowerBounds.get(v), postUpperBounds.get(v))) } ++ frame
    Logger("integer.Transition", LogDebug, "variablesBounds from "+sourcePC+" to "+targetPC+": " + res)
    res
  }
  
  def getPreBounds: Map[Variable,(Option[Int],Option[Int])] = {
    val lowerBounds = Condition.getLowerBounds(guard) ++ getTransientLowerBounds
    val upperBounds = Condition.getUpperBounds(guard) ++ getTransientUpperBounds
    sequencedAllVariables.view.map( v => (v -> (lowerBounds.get(v), upperBounds.get(v))) ).toMap
  }

  //try structural equality
  def same(that: Transition): Boolean = {
    def sameGuard(c1: Condition, c2: Condition): Boolean = (c1, c2) match {
      case (Eq(l1,r1), Eq(l2, r2)) => (l1 == l2 && r1 == r2) || (l1 == r2 && r1 == l2)
      case (Lt(l1,r1), Lt(l2,r2)) => l1 == l2 && r1 == r2
      case (Leq(l1,r1), Leq(l2,r2)) => l1 == l2 && r1 == r2
      case (And(l1,r1), And(l2,r2))=> (sameGuard(l1,l2) && sameGuard(r1,r2)) || (sameGuard(l1,r2) && sameGuard(r1,l2))
      case (Or(l1,r1), Or(l2,r2)) =>  (sameGuard(l1,l2) && sameGuard(r1,r2)) || (sameGuard(l1,r2) && sameGuard(r1,l2))
      case (Not(c1), Not(c2)) => sameGuard(c1,c2)
      case (Literal(b1), Literal(b2)) => b1 == b2
      case _ => false
    }
    def sameUpdates(u1: Seq[Statement], u2: Seq[Statement]): Boolean = {
      u1.forall(s1 => u2 exists (s2 => s1 == s2)) &&
      u2.forall(s2 => u1 exists (s1 => s1 == s2))
    }
    sourcePC == that.sourcePC &&
    targetPC == that.targetPC &&
    sameGuard(guard, that.guard) &&
    sameUpdates(updates, that.updates)
  }


}

object Transition {

  private def compactableLeft(tr: Transition): Boolean = {
    tr.updates forall {
      case Affect(_, _) | Skip => true
      case _ => false
    }
  }

  private def compactLeft(tr1: Transition, tr2: Transition): Transition = {
    assert(tr1.targetPC == tr2.sourcePC, "tr1, tr2 are not connected")
    assert(tr1.sourcePC != tr1.targetPC && tr2.sourcePC != tr2.targetPC, "removing self loop")
    val updatesMap = tr1.updates.flatMap( s => s match {
      case Affect(v, e) => Some(v -> e)
      case Skip => None
      case other => Logger.logAndThrow("integer.Transition", LogError, "not compactable: " + other)
    }).toMap
    val newTr2 = tr2.alphaPre(updatesMap)
    val frame2 = updatesMap -- newTr2.updatedVars //things to add to the second trs
    val resultGuard = And(tr1.guard, newTr2.guard)
    val resultUpdates = newTr2.updates ++ frame2.map{ case (v, e) => Affect(v, e) }
    //println("compactLeft:" +
    //        tr1.updates.filter(_ != Skip).mkString("\n","\n","\n---------") +
    //        tr2.updates.filter(_ != Skip).mkString("\n","\n","\n---------") +
    //        resultUpdates.filter(_ != Skip).mkString("\n","\n","\n========="))
    val res = new Transition(tr1.sourcePC, tr2.targetPC, resultGuard, resultUpdates, tr1.comment + "; " + tr2.comment)
    res.leaner
  }
  
  //try to remove intermediate state (substitution / constrains propagation) while preserving the termination
  def compact(trs: Seq[Transition]): Seq[Transition] = {
    for (i <- 0 until (trs.length -1) ) {
      assert(trs(i).targetPC == trs(i+1).sourcePC, trs)
    }
    if (trs.length <= 1) {
      trs
    } else {
      //first pass: compactLeft
      val (revAcc, last) = ( (List[Transition](), trs.head) /: trs.tail)( ( acc, t2) => {
        val (revAcc, t1) = acc
        if (compactableLeft(t1)) (revAcc, compactLeft(t1, t2))
        else (t1::revAcc, t2)
      })
      //println(last::revAcc)
      (last :: revAcc).reverse
    }
  }
  
}

/** A place where to put the heuritics analysis that we use for simplification */
object TransitionHeuristics {
  
  abstract class VarChange
  case object Fixed extends VarChange //both for stay unchanged and get a constant value
  case object Increase extends VarChange
  case object Decrease extends VarChange
  case object Unknown extends VarChange

  object VarChange {

    def and(v1: VarChange, v2: VarChange) = (v1, v2) match {
      case (Fixed, _) | (_, Fixed) | (Increase, Decrease) | (Decrease, Increase) => Fixed
      case (Increase, _) | (_, Increase) => Increase
      case (Decrease, _) | (_, Decrease) => Decrease
      case _ => Unknown
    }

    def or(v1: VarChange, v2: VarChange) = (v1, v2) match {
      case (Unknown, _) | (_, Unknown) | (Increase, Decrease) | (Decrease, Increase) => Unknown 
      case (Increase, _) | (_, Increase) => Increase
      case (Decrease, _) | (_, Decrease) => Decrease
      case _ => Fixed 
    }

  }

  /** a method to say if a var increase, decrease, ... */
  def variablesChange(t: Transition): Map[Variable, VarChange] = {
    val init: Map[Variable, VarChange] = t.variables.map(v => (v, Unknown)).toMap
    //guards
    lazy val bounds = t.getPreBounds
    //goes over each transition ...
    def processStmt(knowledge: Map[Variable, VarChange], stmt: Statement): Map[Variable, VarChange] = stmt match {
      case Relation(_new, _old) =>
        val (pn,cn) = Expression.decompose(_new)
        if (pn.size == 1) {
          val v = pn.head
          val (po,co) = Expression.decompose(_old)
          val delta = co.i - cn.i
          if (po contains v) {
            //better version ->
            // check that po contains pn, then for the additional variable -> get the lower bounds (since we add)
            // add the var lower bounds and the cst to get the final change
            val other = po.filterNot(_ == v)
            //fetch and sum lower and upper bounds for the other vars
            val (low, up) = ((Some(0): Option[Int], Some(0): Option[Int]) /: other)( (acc, v) => {
              val (vLow, vUp) = bounds(v)
              val newLow = acc._1.flatMap(l => vLow.map(_ + l))
              val newUp = acc._2.flatMap(u => vUp.map(_ + u))
              (newLow, newUp)
            })
            val ch = (low, up) match {
                case (Some(l), Some(u)) =>
                  assert(l <= u)
                  if (l + delta >= 0) {
                    if (u + delta == 0) Fixed else Increase
                  } else {
                    if (u + delta <= 0) Decrease else Unknown
                  }
                case (Some(l), None) => if (l + delta >= 0) Increase else Unknown
                case (None, Some(u)) => if (u + delta <= 0) Decrease else Unknown
                case (None, None) => Unknown
            }
            knowledge + (v -> VarChange.and(knowledge(v), ch))
          } else knowledge
        } else knowledge
      case Variance(_new, _old, greater, strict) if (_old == _new) =>
        if (greater) knowledge + (_new -> VarChange.and(knowledge(_new), Increase))
        else knowledge + (_new -> VarChange.and(knowledge(_new), Decrease))
      case _ => knowledge
    }
    (init /: t.updates)(processStmt)
  }

  /** Tell if a variable is changed by a constant (a maybe some other thing) */
  def constantOffset(t: Transition): Map[Variable, Int] = {
    def processStmt(acc: Map[Variable, Int], stmt: Statement): Map[Variable, Int] = stmt match {
      case Relation(v @ Variable(_), _old) =>
        val (_,co) = Expression.decompose(_old)
        if (co.i != 0) {
          assert(!acc.contains(v))
          acc + (v -> co.i)
        } else {
          acc
        }
      case _ => acc 
    }
    (Map.empty[Variable, Int] /: t.updates)(processStmt)
  }
  
  /** for each var, tell which other var flow into it
   *  TODO better handling of the transients (flow can go through a transient)
   */
  def variableFlow(t: Transition): Map[Variable, Set[Variable]] = {
    val transients = t.transientVariables
    def processStmt(acc: Map[Variable, Set[Variable]], stmt: Statement): Map[Variable, Set[Variable]] = stmt match {
      case Relation(_new, _old) =>
        val (pn,_) = Expression.decompose(_new)
        val (po,_) = Expression.decompose(_old)
        (acc /: pn)( (acc, v) => acc + (v -> (acc.getOrElse(v, Set[Variable]()) ++ po -- transients)) )
      case _ => acc 
    }
    val withSelf = (Map.empty[Variable, Set[Variable]] /: t.updates)(processStmt)
    withSelf.map{ case (k,v) => (k, v - k) }
  }

  def removeSinks(t: Transition, sinks: Set[Variable]): Transition = {
    def removeInCond(c: Condition, pos: Boolean = true): Condition = c match {
      case Eq(l,r) => if ((Expression.variables(l) ++ Expression.variables(r)) exists sinks) Literal(pos) else c
      case Lt(l,r) => if ((Expression.variables(l) ++ Expression.variables(r)) exists sinks) Literal(pos) else c
      case Leq(l,r) => if ((Expression.variables(l) ++ Expression.variables(r)) exists sinks) Literal(pos) else c
      case And(l,r) => And(removeInCond(l, pos), removeInCond(r, pos))
      case Or(l,r) => Or(removeInCond(l, pos), removeInCond(r, pos))
      case Not(c) => Not(removeInCond(c, !pos))
      case Literal(b) => Literal(b)
    }
    def removeInStmt(stmt: Statement): Statement = stmt match {
      case Relation(_new, _old) if (Expression.variables(_new) ++ Expression.variables(_old)) exists sinks => Skip
      case Variance(_new, _old, _, _) if (sinks(_new) || sinks(_old)) => Skip
      case Assume(c) => Assume(removeInCond(c))
      case other => other
    }
    new Transition(t.sourcePC, t.targetPC, removeInCond(t.guard), t.updates map removeInStmt, t.comment)
  }

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

}
