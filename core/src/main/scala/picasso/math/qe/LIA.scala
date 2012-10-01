package picasso.math.qe

import picasso.utils._
import picasso.utils.tools._
import picasso.math.hol._


/** Linear Integer Arithmetic */
object LIA {

  private class SigChecker extends Traverser {
    var result = true
    override def traverse(f: Formula): Unit = {
      super.traverse(f)
      f match {
        case v @ Variable(_) => if (v.tpe != Int) result = false
        case Literal(_: Boolean) =>
        case Literal(_: Int) =>
        case Literal(_) => result = false
        case Application(Times, Literal(_) :: _ :: Nil) =>
        case Application(Minus, _ :: _ :: Nil) =>
        case Application(Plus, _) =>
        case Application(Eq, _ :: _ :: Nil) =>
        case Application(Neq, _ :: _ :: Nil) =>
        case Application(Leq, _ :: _ :: Nil) =>
        case Application(Lt, _ :: _ :: Nil) =>
        case Application(Geq, _ :: _ :: Nil) =>
        case Application(Gt, _ :: _ :: Nil) =>
        case Application(Implies, _ :: _ :: Nil) =>
        case Application(And, _) =>
        case Application(Or, _) =>
        case Application(Not, _) =>
        case Application(_, _) => result = false
        case _ =>
      }
    }
  }
  private class QFSigChecker extends Traverser {
    var result = true
    override def traverse(f: Formula): Unit = {
      super.traverse(f)
      f match {
        case ForAll(_, _) => result = false
        case Exists(_, _) => result = false
        case _ =>
      }
    }
  }

  def isLIA(f: Formula): Boolean = {
    val sg = new SigChecker
    sg.traverse(f)
    sg.result
  }
  
  def isQF(f: Formula): Boolean = {
    val sg = new QFSigChecker
    sg.traverse(f)
    sg.result
  }
  
  def isQFLIA(f: Formula): Boolean = {
    isLIA(f) && isQF(f)
  }

  def qe(universalConstants: Set[Variable], existentialConstants: Set[Variable], f: Formula): Option[Formula] = {
    Logger.assert(isLIA(f), "LIA", f + " not in LIA.")
    //use the Princess thm prover
    princess.Princess.eliminateQuantifiers(
      universalConstants,
      existentialConstants,
      f
    )
  }
  
  def valid(universalConstants: Set[Variable], existentialConstants: Set[Variable], f: Formula): Option[Boolean] = {
    Logger.assert(isLIA(f), "LIA", f + " not in LIA.")
    //try to remove unreferenced quantified variables ...
    val fv = f.freeVariables
    val univ = universalConstants.filter(fv)
    val exist = existentialConstants.filter(fv)
    //try to use an SMT solver rather when possible 
    if (isQF(f) && (univ.isEmpty || exist.isEmpty)) {
      if (univ.isEmpty) {
        sat(f)
      } else {
        sat(Application(Not,List(f))).map(b => !b)
      }
    } else {
      princess.Princess.isValid( univ, exist, f)
    }
  }

  protected def sat(f: Formula): Option[Boolean] = {
    import smtlib._
    Logger.assert(isQFLIA(f), "LIA", f + " not in LIA.")
    val fv = f.freeVariables
    val solver = new Solver(QF_LIA, "z3", Array("-smt2", "-in"))
    for (v <- fv) solver.declare(v)
    solver.assert(f)
    val res = solver.checkSat
    solver.exit
    res
  }

}
