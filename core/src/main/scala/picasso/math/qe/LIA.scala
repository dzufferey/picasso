package picasso.math.qe

import picasso.utils._
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

  def isLIA(f: Formula): Boolean = {
    val sg = new SigChecker
    sg.traverse(f)
    sg.result
  }

  def qe(universalConstants: Set[Variable], existentialConstants: Set[Variable], f: Formula): Option[Formula] = {
    Logger.assert(isLIA(f), "LIA", f + " not in LIA.")
    //use the Princess thm prover
    picasso.utils.tools.princess.Princess.eliminateQuantifiers(
      universalConstants,
      existentialConstants,
      f
    )
  }

}
