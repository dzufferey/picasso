package picasso.model.integer
  
import scala.collection.GenSeq
import picasso.graph._
import picasso.utils._
import picasso.utils.tools.armc._

/** Integer Program.
 *  Integer program are use during the termination proof of DBP.
 *  Right now their purpose is just these termination check (not safety).
 */
class Program2(initPC: String, trs: GenSeq[Transition2]) extends picasso.math.TransitionSystem {
  
  type S = State
  
  //transition type
  type T = Transition2

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

  def simplifyForTermination = {
    Logger("integer.Program", LogDebug, "unsimplified program:")
    Logger("integer.Program", LogDebug, writer => printForARMC(writer) )
    Logger("integer.Program", LogInfo, "propagating constants.")
    val p2 = this.propagateCst
    Logger("integer.Program", LogDebug, writer => p2.printForARMC(writer) )
    Logger("integer.Program", LogInfo, "merging variables.")
    val p3 = p2.reduceNumberOfVariables
    Logger("integer.Program", LogDebug, writer => p3.printForARMC(writer) )
    Logger("integer.Program", LogInfo, "compacting transitions.")
    val p4 = p3.compactPath
    Logger("integer.Program", LogDebug, writer => p4.printForARMC(writer) )
    Logger("integer.Program", LogInfo, "removing duplicate transitions.")
    val p5 = p4.duplicateTransitions
    Logger("integer.Program", LogDebug, writer => p5.printForARMC(writer) )
    p5
    //TODO sinks, ...
  }

  /** Returns a map of which variable has a cst value at some location
   *  Type of the abstract domain: Map[Variable, Option[Int]]
   *  None means it is not cst
   *  Some(i) means it has value i
   *  not in the map means we don't know
   */
  def constantValueMap: Map[String,Map[Variable,Option[Int]]] = {
    def default(s: String) = {
      if (s == initPC) Map[Variable,Option[Int]]( variables.toSeq.map( _ -> None) :_* )
      else Map[Variable,Option[Int]]()
    }

    def transfer(cstMap: Map[Variable,Option[Int]], t: Transition2): Map[Variable,Option[Int]] = {
      val csts = cstMap.flatMap{ case (v,c) => if (t.domain(v)) c.map( v -> _ ) else None }
      val t2 = t.propagteInputConstants(csts)
      val outCst = t2.constantVariables
      cstMap.map{ case (v,_) => (v, if (outCst contains v) Some(outCst(v)) else None)}
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

    cfa.aiFixpoint(transfer, join, cover, default)
  }

  /** propagate the constants values  */
  def propagateCst = {
    val map = constantValueMap
    Logger("integer.Program", LogDebug, "propagateCst: " + map)

    val trs2 = trs.par.map(t => {
      val preSubst = map(t.sourcePC).flatMap{ case (k, v) => v.map(i => (k, i)) }
      t.propagteInputConstants(preSubst)
    })
    new Program2(initPC, trs2)
    
  }

  def reduceNumberOfVariables = {
    //TODO change the way variables and conflicts are computed.
    val trsButInit = trs.filter(_.sourcePC != initialPC)
    val bySrc = trsButInit.groupBy(_.sourcePC)
    val byTrg = trsButInit.groupBy(_.targetPC)
    val locs = pcs - initialPC
    val varsByLoc: Map[String, Set[Variable]] =
      locs.iterator.map( l => {
        val v1 = bySrc(l).flatMap(_.domain)
        val v2 = byTrg(l).flatMap(_.range)
        (l, (v1 ++ v2).seq.toSet)
      }).toMap
    Logger("model.integer", LogNotice, "varsByLoc ->\n  " + varsByLoc.mkString("\n  "))

    //make the conflicts graph with varsByLoc
    val conflictsBase = (DiGraph.empty[GT.ULGT{type V = Variable}] /: variables)(_ + _)
    val conflicts = (conflictsBase /: varsByLoc.values)( (acc, grp) => {
      val edges = for (x <- grp; y <- grp if x != y) yield (x, (), y)
      acc ++ edges
    })
    //use the tranitions to compute the affinity: sum of variables CoI
    val varToIdx = variables.toSeq.zipWithIndex.toMap
    val affinityArray = Array.ofDim[Int](variables.size, variables.size)
    for(t <- trs;
        (v1, vs) <- t.coneOfInfluence;
        v2 <- vs) { 
      affinityArray(varToIdx(v1))(varToIdx(v2)) += 1
      affinityArray(varToIdx(v2))(varToIdx(v1)) += 1
    }
    def affinity(v1: Variable, v2: Variable) = affinityArray(varToIdx(v1))(varToIdx(v2))
    //def affinity(v1: Variable, v2: Variable): Int = Misc.commonPrefix(v1.name, v2.name)
    //small coloring of conflict graph
    val largeClique = varsByLoc.values.maxBy(_.size)
    val coloring = conflicts.smallColoring(affinity, largeClique)
    Logger("model.integer", LogNotice, "coloring ->\n  " + coloring.mkString("\n  "))
    //rename variables
    val globalSubst = (Map[Variable, Variable]() /: coloring)( (acc, grp) => {
      val repr = grp.head
      (acc /: grp)( (map, v) => map + (v -> repr) )
    })
    //-> subst for each loc
    val substByLoc = varsByLoc.map{ case (loc, vars) => (loc, globalSubst.filterKeys(vars contains _)) }
    //-> add frame cstr to transitions that gets new variables
    val trs2 = for (t <- trs) yield {
      //Logger("model.integer", LogNotice, "t -> " + t.toString)
      val srcSubst = if (t.sourcePC == initialPC) globalSubst else substByLoc(t.sourcePC)
      val trgSubst = substByLoc(t.targetPC)
      val woFrame = t.alphaPre(srcSubst).alphaPost(trgSubst)
      //Logger("model.integer", LogNotice, "srcSubst -> " + srcSubst.mkString(", "))
      //Logger("model.integer", LogNotice, "trgSubst -> " + trgSubst.mkString(", "))
      //Logger("model.integer", LogNotice, "woFrame -> " + woFrame.toString)
      val newVars = trgSubst.values.toSet -- woFrame.range
      //TODO what if we need to add the variable ?!
      Logger.assert(newVars forall woFrame.domain, "model.integer", "new vars: " + newVars.mkString(", ") + "\n" + woFrame)
      val cstr = newVars.iterator.map( v => Eq(woFrame.preVars(v),woFrame.postVars(v)) )
      val allCstr = (woFrame.relation /: cstr)(And(_,_))
      new Transition2(
        woFrame.sourcePC,
        woFrame.targetPC,
        woFrame.preVars,
        woFrame.postVars,
        allCstr,
        woFrame.comment
      )
    }
    val p2 = new Program2(initialPC, trs2)
    Logger("integer.Program", LogInfo, "compactPath: #variables before = " + variables.size + ", after = " + p2.variables.size)
    p2
  }
  
  def cfa: EdgeLabeledDiGraph[GT.ELGT{type V = String; type EL = Transition2}] = {
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = Transition2}]
    emp ++ (transitions.map(t => (t.sourcePC, t, t.targetPC)).seq)
  }
  
  protected def compactPath = {
    val trs2 = cfa.simplePaths.flatMap( path => {
      Transition2.compact(path.labels)
    })
    val p2 = new Program2(initPC, trs2)
    Logger("integer.Program", LogInfo, "compactPath: #transitions before = " + transitions.size + ", after = " + p2.transitions.size)
    p2
  }
  
  protected def duplicateTransitions = {
    val grouped = trs.groupBy(_.sourcePC).map(_._2).flatMap(_.groupBy(_.targetPC).map(_._2))
    val pruned = grouped.map( ts => {
      (List[Transition2]() /: ts.seq)( (acc, t) => {
        val acc1 = acc.filter(t2 => !Transition2.lteq(t2,t))
        if (acc1 exists (Transition2.lteq(t, _))) acc1 else t :: acc1
      })
    })
    val trs2 = pruned.seq.flatten.toSeq.par
    val p2 = new Program2(initPC, trs2)
    Logger("integer.Program", LogInfo, "duplicateTransitions: #transitions before = " + transitions.size + ", after = " + p2.transitions.size)
    p2
  }
  
  def candidateRankingFcts: Iterable[Set[Variable]] = {
    //val cyclesIterator = cfa.enumerateSomeCycles
    //val boundedIterator = if (Config.cyclesBound >= 0) cyclesIterator.take(Config.cyclesBound) else cyclesIterator
    //val candidates = boundedIterator.flatMap(c => TransitionHeuristics.transitionPredicates(c.labels))
    //candidates.toSet
    //sys.error("TODO")
    Nil
  }

}

object Program2 {

  def apply(p: Program): Program2 = {
    new Program2(p.initialPC, p.transitions.map(Transition2.apply))
  }

}
