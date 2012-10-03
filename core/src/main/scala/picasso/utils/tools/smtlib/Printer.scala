package picasso.utils.tools.smtlib

import picasso.math.hol._
import picasso.utils._
import java.io._

object Printer {
  
  protected def symbol(i: InterpretedFct) = i match {
    case Implies => "=>"
    case Or => "or"
    case And => "and"
    case Not => "not"
    case Eq => "="
    //case Neq => "!=" -> replace by Not(Eq(...))
    case Geq => ">="
    case Leq => "<="
    case Gt => ">"
    case Lt => "<"
    case Plus => "+"
    case Minus => "-"
    case Times => "*"
    case other => Logger.logAndThrow("smtlib", LogError, "not supported: " + other)
  }

  protected def removeNeq(f: Formula): Formula = f match {
    case Binding(b, vars, f2) => Binding(b, vars, removeNeq(f2))
    case v @ Variable(_) => v
    case l @ Literal(_) => l
    case Application(Neq, args) => Application(Not, List(Application(Eq, args map removeNeq)))
    case Application(fct, args) => Application(fct, args map removeNeq)
    case i: InterpretedFct => i
  }

  def tpe(t: Type): String = t match {
    case Bool => "Bool"
    case Int => "Int"
    case String => "String"
    case Wildcard => "_"
    case Function(args, returns) => args.map(tpe).mkString("(", ") (", ")") + " (" + tpe(returns) + ")"
    case UnInterpreted(id) => id
    case other => Logger.logAndThrow("smtlib", LogError, "not supported: " + other)
  }

  protected def asVar(str: String): String = {
    assert(str.length > 0)
    val noDollars = str.replace("$","_")
    if (noDollars startsWith "_") "v" + noDollars
    else noDollars
  }
  def asVar(v: Variable): String = asVar(v.name)

  protected def asDecl(v: Variable): String = {
    "(" + asVar(v) + " " + tpe(v.tpe) + ")"
  }
  
  protected def printQuantifier(q: String, vars: Iterable[Variable], f: Formula)(implicit writer: BufferedWriter) {
    writer.write("(")
    writer.write(q)
    writer.write(vars.map(asDecl).mkString(" (", " ", ") "))
    printFormula(f)
    writer.write(")")
  }

  protected def printFormula(f: Formula)(implicit writer: BufferedWriter): Unit = f match {
    case Exists(vars, f2) => printQuantifier("exists", vars, f2)
    case ForAll(vars, f2) => printQuantifier("forall", vars, f2)
    case v @ Variable(_) => writer.write(asVar(v))
    case Literal(l: Int) => if (l >= 0) writer.write(l.toString) else writer.write("(- " + (-l).toString + ")")
    case Literal(l) => writer.write(l.toString)
    case Application(fct, args) => 
      writer.write("(")
      printFormula(fct)
      for (a <- args) {
        writer.write(" ")
        printFormula(a)
      }
      writer.write(")")
    case i: InterpretedFct => writer.write(symbol(i))
  }

  def apply(implicit writer: BufferedWriter, f: Formula) {
    printFormula(Formula.flatten(f))
    //writer.newLine
  }

}
