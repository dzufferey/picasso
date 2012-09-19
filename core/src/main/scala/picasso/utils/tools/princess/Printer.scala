package picasso.utils.tools.princess

import picasso.math.hol._
import picasso.utils._
import java.io._

object Printer {

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

  protected def printFormula(f: Formula)(implicit writer: BufferedWriter) = f match {
    case Exists(vars, f2) => 
      sys.error("TODO")
    case ForAll(vars, f2) => 
      sys.error("TODO")
    case v @ Variable(_) => 
      sys.error("TODO")
    case Literal(l) => 
      sys.error("TODO")
    case Application(Times, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(Minus, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(Plus, lst) =>
      sys.error("TODO")
    case Application(Eq, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(Neq, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(Leq, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(Lt, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(Geq, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(Gt, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(Implies, a1 :: a2 :: Nil) =>
      sys.error("TODO")
    case Application(And, lst) =>
      sys.error("TODO")
    case Application(Or, lst) =>
      sys.error("TODO")
    case Application(Not, f2 :: Nil) =>
      sys.error("TODO")
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
