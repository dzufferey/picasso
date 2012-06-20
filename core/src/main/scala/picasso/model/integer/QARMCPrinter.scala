package picasso.model.integer

import java.io._
import scala.collection.GenSeq
import picasso.utils._
import picasso.graph._

object QARMCPrinter extends PrologLikePrinter {

  /* 
  What changes from ARMC:
  transitions are predicate
  the transition relation is defined by combining transition
  then ask QARMC to prove the transition relation disjunctively-well-funded.
  */

  protected val namer = new Namer
  protected val tNames = new java.util.concurrent.ConcurrentHashMap[Transition, String]()
  protected val tNamesReversed = new java.util.concurrent.ConcurrentHashMap[String, Transition]()
  protected def getName(t: Transition): String = {
    if (tNames.containsKey(t)) {
      tNames.get(t)
    } else {
      val n = namer("transition_from_" + t.sourcePC + "_to_" + t.targetPC, true).replace("$","_")
      val res = tNames.putIfAbsent(t, n)
      tNamesReversed.putIfAbsent(n, t)
      if (res == null) n else res
    }
  }

  protected def singleTransition(t: Transition)(implicit writer: BufferedWriter) {
    val name = getName(t)
    val preVar = t.sequencedVariable map asVar
    val postVar = t.sequencedVariable.map(x => asVar(primeVar(x)))
    if (preVar.isEmpty) {
      assert(t.updates forall (_ == Skip), t)
      writer.write("%" + t.comment); writer.newLine
      writer.write(name)
      writer.write(".")
      writer.newLine
    } else {
      writer.write("%" + t.comment); writer.newLine
      writer.write(name)
      writer.write((preVar ++ postVar).mkString("(", ", ", ") :- "))
      val cstr = transitionConstraints(t)
      writer.write(cstr.map(printCondition).mkString("", ", ", "."))
      writer.newLine
    }
  }

  protected def publicPrivateVariablesOfPath(path: Seq[Transition]): (Set[Variable], Set[Variable]) = {
    assert(!path.isEmpty)
    /*
    val first = path.head
    val middle = path.slice(1, path.length - 1)
    val last = path.last
    val privateVars = (Set[Variable]() /: middle)(_ ++ _.variables)
    val publicVars = (first.variables ++ last.variables) -- privateVars
    (publicVars, privateVars)
    */
    val vars = (Set[Variable]() /: path)(_ ++ _.variables)
    (vars , Set[Variable]())
  }

  /** Make a predicate for a simple path.
   *  Returns the name of the predicate and the list of variables it uses.
   */
  protected def simplePath(path: Seq[Transition])(implicit writer: BufferedWriter): (String, Seq[Variable]) = {
    //assumptions about the variables:
    //  the variables of the first and the last state are the only variables
    //  that are modified by other transitions not in this path.
    assert(!path.isEmpty)
    val (publicVars, privateVars) = publicPrivateVariablesOfPath(path)
    val pv = publicVars.toSeq //the public var in a sequence
    val pathName = asLit(namer("path_" + path.head.sourcePC + "_" + path.last.targetPC, true))

    val varNamer = new Namer

    //create the connections between the transitions (variable version) 
    val varsToString = scala.collection.mutable.HashMap[Variable, String]( pv.map(x => (x, asVar(varNamer("X")))): _* )
    val firstVars = varsToString.clone

    val trs = for (t <- path) yield {
      val tv = t.sequencedVariable
      val name = getName(t)
      if (tv.isEmpty) {
        name
      } else {
        val pre = tv.map(v => varsToString.getOrElse(v, asVar(varNamer("X"))) )
        for (v <- tv) varsToString.update(v, asVar(varNamer("X")))
        val post = tv map varsToString
        name + pre.mkString("(", ", ", ", ") + post.mkString("", ", ", ")")
      }
    }

    val pathDecl =
      if (pv.isEmpty) {
        pathName + " :- "
      } else {
        val preVar = pv map firstVars 
        val postVar = pv map varsToString
        pathName + preVar.mkString("(", ", ", ", ") + postVar.mkString("", ", ", ") :- ")
      }
    writer.write(pathDecl)
    writer.write(trs.mkString("", ", ", "."))
    writer.newLine

    (pathName, pv)
  }

  /** Check that the path respects the condition on the variables needed b simplePath. */
  protected def variablesGoodForPath(path: Seq[Transition], other: Seq[Transition]): Boolean = {
    val (publicVars, privateVars) = publicPrivateVariablesOfPath(path)
    val otherVariables = (Set[Variable]() /: other)(_ ++ _.variables)
    (privateVars intersect otherVariables).isEmpty
  }

  protected def predDeclForState(pc: String, preVars: Seq[Variable], postVar: Seq[Variable]) = {
    assert(preVars.length == postVar.length)
    val pre = preVars map printExpression
    val post = postVar map printExpression
    "at_" + asLit(pc) + (pre ++ post).mkString("(",",",")")
  }

  protected def transitionRelation(prog: Program)(implicit writer: BufferedWriter) {
    //connect the transition, figure out what are the variables to use ...
    //  decompose in simple paths
    //  print the paths
    //  connect the paths
    val trs: Seq[Transition] = prog.transitions.seq
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = String}]
    val cfa = emp ++ (trs.map(t => (t.sourcePC, getName(t), t.targetPC)).seq)
    val simpleTraces = cfa.simplePaths
    val simplePaths = simpleTraces.map(_.labels.map(l => tNamesReversed.get(l)))
    for (p <- simplePaths) {
      var others = trs.filterNot(p contains _)
      assert(variablesGoodForPath(p, others), "path: " + p + "\nothers: " + others)
    }
    //all the variables for the global store.
    val vars = prog.variables.toSeq
    //building the transition relation is a bit more complex that just taking the union of all the simple paths
    //the simple paths do not all start and stop at the same place.
    //we need to force that structure ... the easiest way is to use a PC variable
    //can we do better than a PC: yes -> a system of recursive equations
    val junctions = simpleTraces.flatMap(t => { val (a,b) = t.extremities; Seq(a,b) }).toSet
    //val pathStartingAt = junctions.map(pc => (pc -> simplePaths.filter(_.head.sourcePC == pc)) ).toMap
    val pathEndingAt = junctions.map(pc => (pc -> simplePaths.filter(_.last.targetPC == pc)) ).toMap
    //print the simplePaths and get the info
    val pathInfo = simplePaths.map(p => (p -> simplePath(p)) ).toMap
    writer.newLine

    for (state <- junctions) {
      val predecessors = pathEndingAt(state)
      if (predecessors.isEmpty) {
        val pred = predDeclForState(state, vars, vars)
        writer.write(pred + " :- 1=1.")
        writer.newLine
      } else {
        for (path <- predecessors) {
          val (name, pathVars) = pathInfo(path)
          val interVar = vars map primeVar
          val postVar = interVar.map(v => if (pathVars contains v) primeVar(v) else v)
          val source = path.head.sourcePC
          val targetPred = predDeclForState(state, vars, postVar)
          val sourcePred = predDeclForState(source, vars, interVar)
          val pathVars2 = pathVars map primeVar map asVar
          val postPathVar = pathVars map (v => primeVar(primeVar(v))) map asVar
          val pathPred = name + (pathVars2 ++ postPathVar).mkString("(",",",")")
          writer.write(targetPred)
          writer.write(" :- ")
          writer.write(sourcePred)
          writer.write(", ")
          writer.write(pathPred)
          writer.write(".")
          writer.newLine
        }
      }
      /*
      val successors = pathStartingAt(state)
      if (successors.isEmpty) {
        val pred = predDeclForState(state, vars, vars)
        writer.write(pred + " :- 1=1.")
        writer.newLine
      } else {
        for(path <- successors) {
          val (name, pathVars) = pathInfo(path)
          val interVar = vars.map(v => if (pathVars contains v) primeVar(v) else v)
          val postVar = interVar map primeVar 
          val target = path.last.targetPC
          val targetPred = predDeclForState(target, interVar, postVar)
          val sourcePred = predDeclForState(state, vars, postVar)
          val pathVars2 = pathVars map asVar
          val postPathVar = pathVars map primeVar map asVar
          val pathPred = name + (pathVars2 ++ postPathVar).mkString("(",",",")")
          writer.write(sourcePred)
          writer.write(" :- ")
          writer.write(pathPred)
          writer.write(", ")
          writer.write(targetPred)
          writer.write(".")
          writer.newLine
        }
      }
      */
    }

    //what is well-funded ? all the loops
    for (state <- junctions if !pathEndingAt(state).isEmpty) {
      val atJunction = predDeclForState(state, vars, vars map primeVar)
      writer.write("dwf(" + atJunction + ").")
      writer.newLine
    }
    
    /*
    val startPC = prog.initialPC
    assert(junctions(startPC))
    val startRel = predDeclForState(startPC, vars, vars map primeVar)
    writer.write("dwf(" + startRel + ").")
    writer.newLine
    */
  }

  def apply(implicit writer: BufferedWriter, prog: Program) {
    prog.transitions.seq foreach singleTransition
    writer.newLine
    transitionRelation(prog)
    writer.flush
  }

}
