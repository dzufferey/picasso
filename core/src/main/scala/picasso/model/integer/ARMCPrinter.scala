package picasso.model.integer

import java.io._
import scala.collection.GenSeq
import picasso.utils._
import picasso.graph._

object ARMCPrinter extends PrologLikePrinter {

  protected def loc(pc: Option[String], vars: Seq[Variable])(implicit writer: BufferedWriter) {
    val pcString = pc match {
      case Some(s) => "pc(" + asLit(s) + ")"
      case None => "_"
    }
    val data = vars.map(asVar).mkString("",", ","")
    writer.write("p("+ pcString +", data("+ data +"))")
  }
  
  protected def loc(pc: String, vars: Seq[Variable])(implicit writer: BufferedWriter) {
    loc(Some(pc), vars)
  }

  protected def var2names(vars: Seq[Variable])(implicit writer: BufferedWriter) {
    writer.write("var2names( ")
    loc(None, vars)
    writer.write(", [")
    writer.write(vars.map(v => "(" + asVar(v) + ", '" + v.name + "')" ).mkString("",", ",""))
    writer.write("]).")
    writer.newLine
  }

  protected def preds(vars: Seq[Variable])(implicit writer: BufferedWriter) {
    writer.write("preds( ")
    loc(None, vars)
    writer.write(", []).")
    writer.newLine
  }

  protected def start(pc: String)(implicit writer: BufferedWriter) {
    writer.write("start( pc(" + asLit(pc) + ")).")
    writer.newLine
  }

  protected def transPreds(vars: Seq[Variable], prog: Program)(implicit writer: BufferedWriter) {
    val vars2 = vars map primeVar
    writer.write("trans_preds(")
    writer.newLine
    writer.write("  ")
    loc(None, vars)
    writer.write(",  ")
    writer.newLine
    writer.write("  ")
    loc(None, vars2)
    writer.write(",  ")
    writer.newLine
    writer.write("  [")
    val preds = ProgramHeuristics.transitionPredicates(prog)
    val predsStr = preds.flatMap( varSet => {
      val sum1 = varSet.reduceLeft[Expression](Plus(_,_))
      val sum2 = varSet.map(primeVar).reduceLeft[Expression](Plus(_,_))
      val c1 = printCondition( Lt(sum2, sum1) )
      val c2 = printCondition( Eq(sum2, sum1) )
      Seq(c1, c2)
    } )
    val varBoundsStr = preds.flatten.toSet[Variable].map( v => printCondition( Leq(Constant(0), primeVar(v)) ) )
    writer.write((predsStr ++ varBoundsStr).mkString(" ",",\n    ","\n"))
    writer.write("  ]).")
    writer.newLine
  }


  protected def cutpoints(trs: GenSeq[Transition])(implicit writer: BufferedWriter) {
    //find all the cycles in the graph (induced cycles generate the complete cycle space)
    //then set hitting problem (combinatorial optimisation) (can we do is as linear algebra in the cycle space or only as ILP ?)
    val cfa = DiGraph[GT.ULGT{type V = String}](trs.map(t => (t.sourcePC, t.targetPC)).seq)
    //TODO considering all the elementaryCycles is sufficient, but not necessary. We can do better and consider less cycles
    val cycles = cfa.elementaryCycles
    val setsToHit = cycles.map( _.states.toSet )
    //for the moment, use a greedy algorithm ...
    def greedy(candidate: Set[String], toCover: Seq[Set[String]], acc: Set[String]): Set[String] = {
      if (candidate.isEmpty || toCover.isEmpty) {
        assert(toCover.isEmpty)
        acc
      } else {
        val best = candidate.maxBy( x => toCover.filter(_ contains x).length )
        val toCover2 = toCover filterNot (_ contains best)
        greedy(candidate - best, toCover2, acc + best)
      }
    }
    val cutpoints = greedy(cfa.vertices, setsToHit, Set())
    for (pc <- cutpoints) {
        writer.write("cutpoint(pc(" + asLit(pc) + ")).")
        writer.newLine
    }
  }

  protected def constraints(t: Transition, vars: Seq[Variable])(implicit writer: BufferedWriter) {
    //frame since the transition speaks only about the a subset of the variables
    val updatedVars = t.updatedVars
    val frame = vars.filterNot( updatedVars(_) )
    val additionalCstr = frame.map(v => Affect(v, v))
    val readyToPrint = transitionConstraints(t, additionalCstr)
    writer.write(readyToPrint.map(printCondition).mkString("[ ",", ","]"))
  }

  protected def r(t: Transition, idx: Int, vars: Seq[Variable])(implicit writer: BufferedWriter) {
    val vars2 = vars map primeVar
    writer.write("% " + t.comment); writer.newLine
    writer.write("r(  ")
    loc(t.sourcePC, vars)
    writer.write(",")
    writer.newLine
    writer.write("    ")
    loc(t.targetPC, vars2)
    writer.write(",")
    writer.newLine
    writer.write("    ")
    constraints(t, vars)
    writer.write(",")
    writer.newLine
    writer.write("    [], " + idx + ")." )
  }

  def apply(implicit writer: BufferedWriter, prog: Program) {
    val vars = prog.variables.toSeq
    writer.write(preamble); writer.newLine
    var2names(vars); writer.newLine
    preds(vars); writer.newLine
    transPreds(vars, prog); writer.newLine
    start(prog.initialPC)
    cutpoints(prog.transitions); writer.newLine
    for ( (t, idx) <- prog.transitions.seq.zipWithIndex ) {
      r(t, idx, vars)
      writer.newLine
    }
    writer.flush
  }

  protected val preamble = """% BEGIN FIXED PREAMBLE
:- multifile r/5,implicit_updates/0,var2names/2,preds/2,trans_preds/3,
cube_size/1,start/1,error/1,refinement/1,cutpoint/1,invgen_template/2,
invgen_template/1,cfg_exit_relation/1,stmtsrc/2,strengthening/2,globals/3,
bound_var/2,bounding_vars/2,transition_access/2,atomic/3.
refinement(inter).
cube_size(1).
% END FIXED PREAMBLE
"""


}
