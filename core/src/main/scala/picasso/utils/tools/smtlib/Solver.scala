package picasso.utils.tools.smtlib

import picasso.math.hol._
import picasso.utils._
import scala.sys.process._

sealed abstract class Theory
case object QF_LIA
case object LIA
case object QF_LRA
case object LRA

class Solver(th: Theory, cmd: String, options: Iterable[String], implicitDeclaration: Boolean) {

  //TODO solver process -> use JAVA process ???
  //TODO implicit symbol declaration, keep a local stack+set of symbol to know what is declared

  protected var stackCounter = 0

  protected val solverInput = sys.error("TODO")
  protected val solverOutput = sys.error("TODO")

  protected val solver: Process = {
    //(cmd + options.mkString(" ")) #< solverInput #> solverOutput
    sys.error("TODO")
  }

  protected def toSolver(cmd: String) {
    sys.error("TODO")
  }
  
  def declare(t: Type) = t match {
    case UnInterpreted(id) => toSolver("(declare-sort " + id + " 0)")
    case other => Logger.logAndThrow("smtlib", LogError, "not supported: " + other)
  }

  def declare(f: Formula) = f match {
    case v @ Variable(name) =>
      val (args, ret) = v.tpe match {
        case Function(args, r) => (args, r)
        case other => (Nil, other)
      }
      val argsDecl = args.map(Printer.tpe).mkString("("," ",")")
      toSolver("(declare-fun " + name + " " + argsDecl + " " + Printer.tpe(ret) + ")")
    case other => Logger.logAndThrow("smtlib", LogError, "not supported: " + other)
  }
  
  def assert(f: Formula) {
    //(assert f)
    sys.error("TODO")
  }
  
  def push {
    stackCounter += 1
    toSolver("(push 1)")
  }
  
  def pop {
    Logger.assert(stackCounter > 0, "smtlib", "pop -> stackCounter = " + stackCounter)
    toSolver("(pop 1)")
    stackCounter -= 1
  }
  
  def checkSat: Option[Boolean] = {
    sys.error("TODO")
  }

  def exit {
    sys.error("TODO")
  }

}
