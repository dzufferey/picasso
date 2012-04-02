package picasso.model.integer

import java.io._
import scala.collection.GenSeq
import picasso.utils._

object ARMCPrinter {

  protected def asLit(str: String): String = {
    assert(str.length > 0)
    if (str(0).isLower) str
    else str.updated(0, str(0).toLower)
  }
  
  protected def asVar(str: String): String = {
    assert(str.length > 0)
    if (str(0).isUpper) str
    else str.updated(0, str(0).toUpper)
  }
  protected def asVar(v: Variable): String = asVar(v.name)

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
    writer.write(vars.map(v => "(" + asVar(v) + ", '" + v.name + "'" ).mkString("",", ",""))
    writer.write("]).")
    writer.newLine
  }

  protected def preds(vars: Seq[Variable])(implicit writer: BufferedWriter) {
    writer.write("preds( ")
    loc(None, vars)
    writer.write(", []).")
    writer.newLine
  }

  protected def cutpoints(trs: GenSeq[Transition])(implicit writer: BufferedWriter) {
    //find all the cycles in the graph (induced cycles generate the complete cycle space)
    //then set hitting problem (combinatorial optimisation) / can we do is as linear algebra in the cycle space ?
    /*
cutpoint(pc(l0)).
cutpoint(pc(l1)).
cutpoint(pc(l2)).
cutpoint(pc(l3)).
    */
    sys.error("TODO")
  }

  protected def primeVar(v: Variable): Variable = Variable(v.name + "_prime")

  protected def primeNotTransient(e: Expression, transient: Set[Variable]): Expression = e match {
    case Plus(l,r) => Plus(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Minus(l,r) => Minus(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case UMinus(u) => UMinus(primeNotTransient(u, transient))
    case c @ Constant(_) => c
    case v @ Variable(_) => if (transient(v)) v else primeVar(v)
  }

  protected def primeNotTransient(c: Condition, transient: Set[Variable]): Condition = c match {
    case Eq(l,r) => Eq(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Lt(l,r) => Lt(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Leq(l,r) => Leq(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case And(l,r) => And(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Or(l,r) => Or(primeNotTransient(l, transient), primeNotTransient(r, transient))
    case Not(c) => Not(primeNotTransient(c, transient))
    case l @ Literal(_) => l
  }

  protected def printCondition(c: Condition): String = c match {
    case Eq(l,r) =>  Expression.print(l) + " = " + Expression.print(r)
    case Lt(l,r) =>  Expression.print(l) + " < " + Expression.print(r)
    case Leq(l,r) => Expression.print(l) + " =< " + Expression.print(r)
    case And(l,r) => printCondition(l) + ", " + printCondition(r) 
    case err @ Or(l,r) => Logger.logAndThrow("ARMC", LogError, "Or not yet supported:  " + err)
    case err @ Not(c) =>  Logger.logAndThrow("ARMC", LogError, "Not not yet supported:  " + err)
    case Literal(b) => if (b) "0 = 0" else "1 = 0"
  }

  protected def makeConditionNice(c: Condition): Seq[Condition] = {
    //flatten the And, remove the literals, ... 
    def flatten(c: Condition, acc: List[Condition]): List[Condition] = c match {
      case And(l,r) => flatten(r, flatten(l, acc))
      case err @ Or(l,r) => Logger.logAndThrow("ARMC", LogError, "Or not yet supported:  " + err)
      case err @ Not(c) =>  Logger.logAndThrow("ARMC", LogError, "Not not yet supported:  " + err)
      case Literal(b) => if (b) acc else List(Literal(false))
      case other => other :: acc
    }
    flatten(Condition.nnf(c), Nil)
  }

  protected def constraints(guard: Condition, stmts: Seq[Statement], transient: Set[Variable])(implicit writer: BufferedWriter) {
    val readyToPrint = guard +: (stmts flatMap {
      case Skip | Transient(_) => Seq()
      case Relation(n, o) => makeConditionNice(Eq(primeNotTransient(n, transient), o))
      case Assume(c) => makeConditionNice(primeNotTransient(c, transient))
    })
    writer.write(readyToPrint.map(printCondition).mkString("[ ",", ","]"))
    writer.newLine
  }

  protected def r(t: Transition, idx: Int, vars: Seq[Variable])(implicit writer: BufferedWriter) {
    val vars2 = vars map primeVar
    //frame since the transition speaks only about the a subset of the variables
    val updatedVars = t.updatedVars
    val frame = vars.filterNot( updatedVars(_) )
    val additionalCstr = frame.map(v => Affect(v, v))
    val allTrs = t.updates ++ additionalCstr

    writer.write("r( ")
    loc(t.sourcePC, vars)
    writer.write(", ")
    loc(t.targetPC, vars2)
    writer.write(", ")
    constraints(t.guard, allTrs, t.transientVariables)
    writer.write(", [], " + idx + ")." )
  }

  protected def apply(implicit writer: BufferedWriter, prog: Program) {
    val vars = prog.variables.toSeq
    writer.write(preamble); writer.newLine
    var2names(vars); writer.newLine
    preds(vars); writer.newLine
    cutpoints(prog.transitions); writer.newLine
    for ( (t, idx) <- prog.transitions.seq.zipWithIndex ) {
      r(t, idx, vars)
      writer.newLine
    }
  }

  val preamble = """% BEGIN FIXED PREAMBLE
:- multifile r/5,implicit_updates/0,var2names/2,preds/2,trans_preds/3,
cube_size/1,start/1,error/1,refinement/1,cutpoint/1,invgen_template/2,
 invgen_template/1,cfg_exit_relation/1,stmtsrc/2,strengthening/2,globals/3,
 bound_var/2,bounding_vars/2,transition_access/2,atomic/3.
refinement(inter).
cube_size(1).
% END FIXED PREAMBLE
"""


}
