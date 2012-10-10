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

  lazy val varsByLoc: Map[String, Set[Variable]] = {
    val bySrc = trs.groupBy(_.sourcePC)
    val byTrg = trs.groupBy(_.targetPC)
    pcs.iterator.map( l => {
      val v1 = bySrc.get(l).map(_.flatMap(_.domain).seq)
      val v2 = byTrg.get(l).map(_.flatMap(_.range).seq)
      (l, (v1 ++ v2).flatten.toSet)
    }).toMap
  }
  
  def printForARMCnoPreds(writer: java.io.BufferedWriter) {
    ARMCPrinter(writer, this, false)
    writer.flush
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
    Logger("integer.Program", LogDebug, writer => printForARMCnoPreds(writer) )
    Logger("integer.Program", LogInfo, "eliminating variables: " + Config.eliminateVar.mkString(", "))
    val p1 = this.eliminateVariables(Config.eliminateVar)
    Logger("integer.Program", LogDebug, writer => p1.printForARMCnoPreds(writer) )
    Logger("integer.Program", LogInfo, "propagating constants.")
    val p2 = p1.propagateCst
    Logger("integer.Program", LogDebug, writer => p2.printForARMCnoPreds(writer) )
    Logger("integer.Program", LogInfo, "merging variables.")
    val p3 = p2.reduceNumberOfVariables
    Logger("integer.Program", LogDebug, writer => p3.printForARMCnoPreds(writer) )
    //this.infos
    //p2.infos
    //p3.infos
    Logger("integer.Program", LogInfo, "compacting transitions.")
    val p4 = p3.compactPath
    Logger("integer.Program", LogDebug, writer => p4.printForARMCnoPreds(writer) )
    Logger("integer.Program", LogInfo, "removing duplicate transitions.")
    val p5 = p4.duplicateTransitions
    Logger("integer.Program", LogDebug, writer => p5.printForARMCnoPreds(writer) )
    p5
    //TODO sinks, ...
  }
  def eliminateVariables(prefixes: Iterable[String]) = {
    if (prefixes.isEmpty) {
      this
    } else {
      val trs2 = trs.map(_.eliminateVariables(prefixes))
      val p2 = new Program2(initialPC, trs2)
      Logger("integer.Program", LogInfo, "eliminateVariables: #variables before = " + variables.size + ", after = " + p2.variables.size)
      p2
    }
  }

  /** Returns a map of which variable has a cst value at some location
   *  Type of the abstract domain: Map[Variable, Option[Int]]
   *  None means it is not cst
   *  Some(i) means it has value i
   *  not in the map means we don't know
   */
  def constantValueMap: Map[String,Map[Variable,Option[Int]]] = {

    def default(s: String) = Map[Variable,Option[Int]]()

    def transfer(cstMap: Map[Variable,Option[Int]], t: Transition2): Map[Variable,Option[Int]] = {
      val csts = cstMap.flatMap{ case (v,c) => c.map( v -> _ ) }
      val t2 = t.propagteInputConstants(csts)
      val outCst = t2.constantVariables
      val frame = cstMap -- t.range
      val unk = t.range -- outCst.keySet
      frame ++ outCst.map{ case (v, c) => v -> Some(c) } ++ unk.iterator.map(_ -> None)
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
      val postSubst = map(t.targetPC).flatMap{ case (k, v) => v.map(_ => k) }.toSet
      val t2 = t.propagteInputConstants(preSubst).propagteOutputConstants(postSubst)
      //Logger("integer.Program", LogDebug, "eliminating: " + postSubst.mkString(", ") + "\nin " + t + "\ngives " + t2)
      t2
    })
    val p2 = new Program2(initPC, trs2)
    Logger("integer.Program", LogInfo, "propagateCst: #variables before = " + variables.size + ", after = " + p2.variables.size)
    p2
  }

  def reduceNumberOfVariables = {
    //TODO this creates unused and unconstrained variables
    //TODO for some reason, i does no decrease the number of variables ...
    val varsByLocButInit = varsByLoc - initialPC
    Logger("model.integer", LogDebug, "varsByLocButInit ->\n  " + varsByLocButInit.mkString("\n  "))
    //make the conflicts graph with varsByLoc
    val conflictsBase = (DiGraph.empty[GT.ULGT{type V = Variable}] /: variables)(_ + _)
    val conflicts = (conflictsBase /: varsByLocButInit.values)( (acc, grp) => {
      val edges = for (x <- grp; y <- grp if x != y) yield (x, (), y)
      acc ++ edges
    })
    //use the tranitions to compute the affinity: sum of variables CoI + name likenes
    val varToIdx = variables.toSeq.zipWithIndex.toMap
    val affinityArray = Array.ofDim[Int](variables.size, variables.size)
    for(t <- trs;
        (v1, vs) <- t.coneOfInfluence;
        v2 <- vs) { 
      affinityArray(varToIdx(v1))(varToIdx(v2)) += 1
      affinityArray(varToIdx(v2))(varToIdx(v1)) += 1
    }
    def affinity(v1: Variable, v2: Variable) = {
      affinityArray(varToIdx(v1))(varToIdx(v2)) +
      Misc.commonPrefix(v1.name, v2.name)
    }
    //small coloring of conflict graph
    val largeClique = varsByLocButInit.values.maxBy(_.size)
    Logger("integer.Program", LogDebug, "reduceNumberOfVariables: largeClique has size = " + largeClique.size )
    val coloring = conflicts.smallColoring(affinity, largeClique)
    Logger("model.integer", LogDebug, "coloring ->\n  " + coloring.mkString("\n  "))
    //rename variables
    val globalSubst = (Map[Variable, Variable]() /: coloring)( (acc, grp) => {
      val repr = grp.head
      (acc /: grp)( (map, v) => map + (v -> repr) )
    })
    //-> subst for each loc
    val substByLoc = varsByLocButInit.map{ case (loc, vars) => (loc, globalSubst.filterKeys(vars contains _)) }
    //TODO initialPC
    //-> add frame cstr to transitions that gets new variables
    val trs2 = for (t <- trs) yield {
      //Logger("model.integer", LogNotice, "t -> " + t.toString)
      val srcSubst = if (t.sourcePC == initialPC) globalSubst else substByLoc(t.sourcePC)
      val trgSubst = substByLoc(t.targetPC)
      val woFrame = t.alphaPre(srcSubst).alphaPost(trgSubst)
      //Logger("model.integer", LogNotice, "srcSubst -> " + srcSubst.mkString(", "))
      //Logger("model.integer", LogNotice, "trgSubst -> " + trgSubst.mkString(", "))
      //Logger("model.integer", LogNotice, "woFrame -> " + woFrame.toString)
      val newPreVars = srcSubst.values.toSet -- woFrame.domain
      val newPostVars = trgSubst.values.toSet -- woFrame.range
      val preVars2 = woFrame.preVars ++ newPreVars.iterator.map( v => (v, Variable(Namer("NewPreVar"))) )
      val postVars2 = woFrame.postVars ++ newPostVars.iterator.map( v => (v, Variable(Namer("NewPostVar"))) )
      //val cstr = newPostVars.iterator.map( v => Eq(preVars2(v), postVars2(v)) )
      //val allCstr = (woFrame.relation /: cstr)(And(_,_))
      new Transition2(
        woFrame.sourcePC,
        woFrame.targetPC,
        preVars2,
        postVars2,
        woFrame.relation,//allCstr,
        woFrame.comment
      )
    }
    val p2 = new Program2(initialPC, trs2)
    Logger("integer.Program", LogInfo, "reduceNumberOfVariables: #variables before = " + variables.size + ", after = " + p2.variables.size)
    p2
  }
  
  def cfa: EdgeLabeledDiGraph[GT.ELGT{type V = String; type EL = Transition2}] = {
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = Transition2}]
    emp ++ (transitions.map(t => (t.sourcePC, t, t.targetPC)).seq)
  }
  
  protected def compactPath = {
    val trs2 = cfa.simplePaths.toSeq.par.flatMap( path => {
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

//protected def flow: DiGraph[GT.ULGT{type V = Variable}] = {
//  //try to track what is going where ...
//  sys.error("TODO")
//}

  protected def transfers: DiGraph[GT.ULGT{type V = Variable}] = {
    val base = DiGraph.empty[GT.ULGT{type V = Variable}].addVertices(variables)
    val edges = for (t <- trs; (v1, vs) <- t.coneOfInfluence; v2 <- vs) yield (v1, (), v2)
    base ++ edges.seq
  }

  protected def infos {
    val lvl = LogInfo
    Logger("integer.Program", lvl, "#variables = " + variables.size )
    Logger("integer.Program", lvl, "#transitions = " + transitions.size )
    Logger("integer.Program", lvl, transfers.toGraphviz("transfers"))
    for(t <- transitions) {
      val frame = variables -- t.variables
      val unused = t.unusedVariable
      val unconstrained = t.unconstrainedVariables
      Logger(
        "integer.Program", lvl,
        "from " + t.sourcePC + " to " + t.targetPC + ": " + t.comment + "\n" +
        "frame: " + frame.mkString(", ") + "\n" +
        "domain: " + t.domain.mkString(", ") + "\n" +
        "range: " + t.range.mkString(", ") + "\n" +
        "unused: " + unused.mkString(", ") + "\n" +
        "unconstrained: " + unconstrained.mkString(", ")
      )
    }
    //Logger("integer.Program", lvl, writer => printForARMCnoPreds(writer) )
  }
  
  def candidateRankingFcts: Iterable[Set[Variable]] = {
    val cyclesIterator = cfa.enumerateSomeCycles
    val boundedIterator = if (Config.cyclesBound >= 0) cyclesIterator.take(Config.cyclesBound) else cyclesIterator
    val candidates = boundedIterator.flatMap(c => Transition2.candidateRankingFcts(c.labels))
    candidates.toSet
  }

}

object Program2 {

  def apply(p: Program): Program2 = {
    new Program2(p.initialPC, p.transitions.map(Transition2.apply))
  }

}
