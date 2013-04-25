package picasso.utils.tools.nts

import picasso.utils.tools.armc.PrologLikePrinter
import picasso.model.integer._
import java.io._
import scala.collection.GenSeq
import picasso.utils._
import picasso.graph._

object NTSPrinter extends PrologLikePrinter {
  
  override protected def primeVar(v: Variable): Variable = Variable(v.name + "'")
  
  //TODO priorities
  override protected def printCondition(c: Condition): String = c match {
    case Eq(l,r) =>  printExpression(l) + " = " + printExpression(r)
    case Lt(l,r) =>  printExpression(l) + " < " + printExpression(r)
    case Leq(l,r) => printExpression(l) + " <= " + printExpression(r)
    case And(lst) => lst.map(printCondition).mkString(" and ")
    case Or(lst) => lst.map(printCondition).mkString(" or ")
    case Not(c) => "not " + printCondition(c)
    case Literal(b) => if (b) "true" else "false"
  }

  protected def declareVars(vars: Seq[Variable])(implicit writer: BufferedWriter) {
    writer.write(vars.map(v => asVar(v)).mkString("  ",", "," : int;"))
    writer.newLine
  }

  protected def start(pc: String)(implicit writer: BufferedWriter) {
    writer.write("  initial " + asLit(pc) + ";")
    writer.newLine
  }
  
  protected def end(pc: String)(implicit writer: BufferedWriter) {
    writer.write("  final " + asLit(pc) + ";")
    writer.newLine
  }
  
  protected def r(t: Transition, vars: Seq[Variable])(implicit writer: BufferedWriter) {
    val frame = vars.filterNot( t.range(_) ).toList
    //val additionalCstr = frame.map(v => Eq(v, primeVar(v)))
    val additionalCstr = frame.map(v => Eq(primeVar(v), Constant(0) ))
    val pre = vars.iterator.map( v => (v,v) ).toMap
    val post = vars.iterator.map( v => (v,primeVar(v)) ).toMap
    val subst = t.substForRelation(pre, post)
    val relation = And(Condition.alpha(t.relation, subst) :: additionalCstr)
    writer.write("  // " + t.comment)
    writer.newLine
    writer.write("  " + asLit(t.sourcePC) + " -> " + asLit(t.targetPC) + " { " + printCondition(relation) + " }")
    writer.newLine
  }

  protected val header = "nts someNTS; main {"
  protected val footer = "}"
  
  def apply(implicit writer: BufferedWriter, prog: Program) {
    val vars = prog.variables.toSeq
    val finalState = "final_state"
    writer.write(header); writer.newLine
    declareVars(vars)
    start(prog.initialPC)
    end(finalState)
    writer.newLine
    for ( t <- prog.transitions.seq) {
      r(t, vars)
      writer.newLine
    }
    for (l <- prog.pcs) {
      writer.write("  // to final state"); writer.newLine
      writer.write("  " + asLit(l) + " -> " + asLit(finalState) + " { havoc() }")
      writer.newLine
    }
    writer.write(footer); writer.newLine
    writer.flush
  }

  def asString(prog: Program) = {
    val str = new java.io.StringWriter()
    val writer = new java.io.BufferedWriter(str)
    apply(writer, prog)
    writer.close
    str.toString
  }

}
