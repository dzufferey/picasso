package picasso.utils.tools.princess

import picasso.math.hol._
import picasso.utils._
import java.io._

object Printer {

  protected def unary(i: InterpretedFct) = i match {
    case Not => true
    case _ => false
  }

  protected def binary(i: InterpretedFct) = i match {
    case Implies => true 
    case Or | And | Not => false 
    case Eq | Neq | Geq | Leq | Gt | Lt => true
    case Plus | Minus | Times => false
    case other => Logger.logAndThrow("princess", LogError, "don't know the priority of " + other)
  }

  protected def priority(i: InterpretedFct) = i match {
    case Implies => 0
    case Or => 1
    case And => 2
    case Not => 3
    case Eq | Neq | Geq | Leq | Gt | Lt => 4
    case Plus | Minus => 5
    case Times => 6
    case other => Logger.logAndThrow("princess", LogError, "don't know the priority of " + other)
  }

  protected def symbol(i: InterpretedFct) = i match {
    case Implies => "->"
    case Or => "|"
    case And => "&"
    case Not => "!"
    case Eq => "="
    case Neq => "!="
    case Geq => ">="
    case Leq => "<="
    case Gt => ">"
    case Lt => "<"
    case Plus => "+"
    case Minus => "-"
    case Times => "*"
    case other => Logger.logAndThrow("princess", LogError, "not supported: " + other)
  }

  protected def asVar(str: String): String = {
    assert(str.length > 0)
    val noDollars = str.replace("$","_")
    if (noDollars startsWith "_") "v" + noDollars
    else noDollars
  }
  protected def asVar(v: Variable): String = asVar(v.name)

  protected def cstDecl(what: String, vars: Iterable[Variable])(implicit writer: BufferedWriter) {
    writer.write("\\"+what+" {")
    writer.newLine
    for(v <- vars) {
      writer.write("  int " + asVar(v) + ";")
      writer.newLine
    }
    writer.write("}")
    writer.newLine
  }

  protected def univCst(vars: Iterable[Variable])(implicit writer: BufferedWriter) {
    cstDecl("universalConstants", vars)
  }
  
  protected def exitCst(vars: Iterable[Variable])(implicit writer: BufferedWriter) {
    cstDecl("existentialConstants", vars)
  }

  protected def printQuantifier(q: String, vars: Iterable[Variable], f: Formula)(implicit writer: BufferedWriter) {
    writer.write("\\"+q+" int ")
    writer.write(vars.map(asVar).mkString(", "))
    writer.write("; ")
    printFormula(f, priority(Not))
  }

  protected def printApplication(fct: InterpretedFct, args: List[Formula], priority1: Int = -1)(implicit writer: BufferedWriter) {
    val priority2 = priority(fct)
    val sym = symbol(fct)
    if (priority2 <= priority1) writer.write("( ")
    if (unary(fct)) {
      Logger.assert(args.size == 1, "princess", "wrong arity for " + fct + ": " + args)
      writer.write(sym + " ")
      printFormula(args(0), priority2)
    } else if (binary(fct)) {
      Logger.assert(args.size == 2, "princess", "wrong arity for " + fct + ": " + args)
      printFormula(args(0), priority2)
      writer.write(" " + sym + " ")
      printFormula(args(1), priority2)
    } else {
      Logger.assert(!args.isEmpty, "princess", "wrong arity for " + fct + ": " + args)
      sys.error("TODO")
    }
    if (priority2 <= priority1) writer.write(" )")
  }

  protected def printFormula(f: Formula, currPriority: Int = -1)(implicit writer: BufferedWriter) = f match {
    case Exists(vars, f2) => printQuantifier("exists", vars, f2)
    case ForAll(vars, f2) => printQuantifier("forall", vars, f2)
    case v @ Variable(_) => writer.write(asVar(v))
    case Literal(l) => writer.write(l.toString)
    case Application(fct: InterpretedFct, args) => printApplication(fct, args, currPriority)
    case other => Logger.logAndThrow("princess", LogError, "don't know what to do with " + other)
  }
  
  def apply(implicit writer: BufferedWriter, universalConstants: Set[Variable], existentialConstants: Set[Variable], f: Formula) {
    univCst(universalConstants)
    writer.newLine
    exitCst(existentialConstants)
    writer.newLine
    writer.write("\\problem {")
    writer.write("  ")
    printFormula(f)
    writer.newLine
    writer.write("}")
    writer.newLine
  }
}
