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
      val n = namer("transition_" + t.sourcePC + "_" + t.targetPC).replace("$","_")
      val res = tNames.putIfAbsent(t, n)
      tNamesReversed.putIfAbsent(n, t)
      if (res == null) n else res
    }
  }

  protected def singleTransition(t: Transition)(implicit writer: BufferedWriter) {
    val name = getName(t)
    val preVar = t.sequencedVariable map asVar
    val postVar = t.sequencedVariable.map(x => asVar(primeVar(x)))
    assert(!preVar.isEmpty)
    writer.write("%" + t.comment); writer.newLine
    writer.write(name)
    writer.write(preVar.mkString("(", ", ", ", "))
    writer.write(postVar.mkString("", ", ", ") :- "))
    val cstr = transitionConstraints(t)
    writer.write(cstr.mkString("", ", ", "."))
    writer.newLine
  }

  protected def publicPrivateVariablesOfPath(path: Seq[Transition]): (Set[Variable], Set[Variable]) = {
    assert(!path.isEmpty)
    val first = path.head
    val middle = path.slice(1, path.length - 1)
    val last = path.last
    val privateVars = (Set[Variable]() /: middle)(_ ++ _.variables)
    val publicVars = (first.variables ++ last.variables) -- privateVars
    (publicVars, privateVars)
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
    val pathName = namer("path_" + path.head.sourcePC + "_" + path.last.targetPC)

    //create the connections between the transitions (variable version) 
    val varsToString = scala.collection.mutable.HashMap[Variable, String]( pv.map(x => (x, asVar(namer(x.name, true)))): _* )

    val trs = for (t <- path) yield {
      val tv = t.sequencedVariable
      val pre = tv.map(v => varsToString.getOrElse(v, asVar(namer(v.name, true))) )
      for (v <- tv) varsToString.update(v, asVar(namer(v.name, true)))
      val post = tv map varsToString
      getName(t) + pre.mkString("(", ", ", ", ") + post.mkString("", ", ", ")")
    }

    val preVar = pv
    val postVar = pv map varsToString
    val pathDecl = pathName + preVar.mkString("(", ", ", ", ") + postVar.mkString("", ", ", ") :- ")
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

  protected def transitionRelation(trs: Seq[Transition])(implicit writer: BufferedWriter) {
    //connect the transition, figure out what are the variables to use ...
    //  decompose in simple paths
    //  print the paths
    //  connect the paths
    val emp = EdgeLabeledDiGraph.empty[GT.ELGT{type V = String; type EL = String}]
    val cfa = emp ++ (trs.map(t => (t.sourcePC, getName(t) , t.targetPC)).seq)
    val simplePaths = cfa.simplePaths.map(_.labels.map(l => tNamesReversed.get(l)))
    for (p <- simplePaths) {
      var others = trs.filterNot(p contains _)
      assert(variablesGoodForPath(p, others))
    }
    //TODO
    sys.error("TODO")
  }

  def apply(implicit writer: BufferedWriter, prog: Program) {
    sys.error("TODO")
    writer.flush
  }

}
