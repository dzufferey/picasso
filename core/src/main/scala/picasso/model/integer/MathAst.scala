package picasso.model.integer

import picasso.utils._
import picasso.math._

object ToMathAst {

  def apply(e: Expression): hol.Formula = e match {
    case Plus(l,r) => hol.Application(hol.Plus, List(apply(l), apply(r)))
    case Minus(l,r) => hol.Application(hol.Minus, List(apply(l), apply(r)))
    case Constant(c) => hol.Literal(c).setType(hol.Int)
    case Variable(v) => hol.Variable(v).setType(hol.Int)
  }
  
  def variable(v: Variable): hol.Variable = {
    hol.Variable(v.name).setType(hol.Int)
  }
  
  //works only on SSA statements
  def apply(s: Statement): hol.Formula = {
    Logger.assert(
      Statement.getReadVariables(s).intersect(Statement.getUpdatedVars(s)).isEmpty,
      "integer.MathAst", "apply works only on SSA."
    )
    s match {
      case Transient(v) =>
        Logger("integer.MathAst", LogWarning, "found Transient: " + v)
        hol.Literal(true).setType(hol.Int)
      case Skip =>
        hol.Literal(true).setType(hol.Int)

      case Relation(_new, _old) =>
        hol.Application(hol.Eq, List(apply(_old), apply(_new)))

      case Assume(c) =>
        apply(c)

      case Variance(_new, _old, geq, strict) =>
        val fct = if (geq) {
          if (strict) hol.Gt
          else hol.Geq
        } else {
          if (strict) hol.Lt
          else hol.Leq
        }
        hol.Application(fct, List(apply(_new), apply(_old)))
    }
  }
  
  def apply(c: Condition): hol.Formula = c match {
    case Eq(l,r) => hol.Application(hol.Eq, List(apply(l), apply(r)))
    case Lt(l,r) => hol.Application(hol.Lt, List(apply(l), apply(r)))
    case Leq(l,r) => hol.Application(hol.Leq, List(apply(l), apply(r)))
    case And(l,r) => hol.Application(hol.And, List(apply(l), apply(r)))
    case Or(l,r) => hol.Application(hol.Or, List(apply(l), apply(r)))
    case Not(c) => hol.Application(hol.Not, List(apply(c)))
    case Literal(l) => hol.Literal(l).setType(hol.Bool)
  }

}

object FromMathAst {

  def variable(v: hol.Variable): Variable = {
    Variable(v.name)
  }

  def expression(f: hol.Formula): Expression = f match {
    case hol.Application(fct, args) =>
      val args2 = args map expression
      fct match {
        case hol.Plus => args2.reduceLeft(Plus(_, _))
        case hol.Minus => args2.reduceLeft(Minus(_,_))
        case hol.Times =>
          Logger.assert( args2.size == 2, "integer.MathAst",
            "FromMathAst, Times with " + args2 )
          args2(0) match {
            case Constant(c) =>
              if (c > 0) (0 until c).map(_ => args2(1)).reduceLeft(Plus(_, _))
              if (c == 0) Constant(0)
              else ((Constant(0): Expression) /: (0 until -c).map(_ => args2(1)))(Minus(_, _))
            case other => Logger.logAndThrow("integer.MathAst", LogError, "FromMathAst.expression, expected Constant found: " + other)
          }
        case other => Logger.logAndThrow("integer.MathAst", LogError, "FromMathAst.expression fct: " + other)
      }
    case hol.Literal(l: Int) => Constant(l)
    case hol.Variable(v) => Variable(v)
    case other => Logger.logAndThrow("integer.MathAst", LogError, "FromMathAst.expression: " + other)
  }

  protected def inEq(greater: Boolean, strict: Boolean, args: List[hol.Formula]): Condition = {
    Logger.assert( args.size == 2, "integer.MathAst", "FromMathAst, inEq with " + args )
    val a1 = expression(args(0))
    val a2 = expression(args(1))
    val (small,big) = if (greater) (a2, a1) else (a1, a2)
    if (strict) Lt(small, big) else Leq(small, big)
  }

  def apply(f: hol.Formula): Condition = f match {
    case hol.Application(fct, args) =>
      fct match {
        case hol.And => (args.iterator map apply).reduceLeft(And(_, _))
        case hol.Or =>  (args.iterator map apply).reduceLeft(Or(_, _))
        case hol.Not => 
          Logger.assert( args.size == 1, "integer.MathAst",
            "FromMathAst, Not with " + args )
          Not(apply(args(0)))
        case hol.Implies => 
          Logger.assert( args.size == 2, "integer.MathAst",
            "FromMathAst, Implies with " + args )
          Or(Not(apply(args(0))), apply(args(1)))

        case hol.Eq =>
          Logger.assert( args.size == 2, "integer.MathAst",
            "FromMathAst, Eq with " + args )
          Eq(expression(args(0)), expression(args(1)))
        case hol.Neq => 
          Logger.assert( args.size == 2, "integer.MathAst",
            "FromMathAst, Neq with " + args )
          Not(Eq(expression(args(0)), expression(args(1))))
        case hol.Geq => inEq(true, false, args)
        case hol.Leq => inEq(false, false, args)
        case hol.Gt => inEq(true, true, args)
        case hol.Lt => inEq(false, true, args)
        case other => Logger.logAndThrow("integer.MathAst", LogError, "FromMathAst fct: " + other)
      }
    case hol.Literal(l: Boolean) => Literal(l)
    case other => Logger.logAndThrow("integer.MathAst", LogError, "FromMathAst: " + other)
  }

}
