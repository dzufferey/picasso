package picasso.model.integer

import picasso.utils._

object ToMathAst {

  def apply(e: Expression): picasso.math.hol.Formula = e match {
    case Plus(l,r) => picasso.math.hol.Application(picasso.math.hol.Plus, List(apply(l), apply(r)))
    case Minus(l,r) => picasso.math.hol.Application(picasso.math.hol.Minus, List(apply(l), apply(r)))
    case Constant(c) => picasso.math.hol.Literal(c).setType(picasso.math.hol.Int)
    case Variable(v) => picasso.math.hol.Variable(v).setType(picasso.math.hol.Int)
  }
  
  def variable(v: Variable): picasso.math.hol.Variable = {
    picasso.math.hol.Variable(v.name).setType(picasso.math.hol.Int)
  }
  
  //works only on SSA statements
  def apply(s: Statement): picasso.math.hol.Formula = {
    Logger.assert(
      Statement.getReadVariables(s).intersect(Statement.getUpdatedVars(s)).isEmpty,
      "integer.MathAst", "apply works only on SSA."
    )
    s match {
      case Transient(v) =>
        Logger("integer.MathAst", LogWarning, "found Transient: " + v)
        picasso.math.hol.Literal(true).setType(picasso.math.hol.Int)
      case Skip =>
        picasso.math.hol.Literal(true).setType(picasso.math.hol.Int)

      case Relation(_new, _old) =>
        picasso.math.hol.Application(picasso.math.hol.Eq, List(apply(_old), apply(_new)))

      case Assume(c) =>
        apply(c)

      case Variance(_new, _old, geq, strict) =>
        val fct = if (geq) {
          if (strict) picasso.math.hol.Gt
          else picasso.math.hol.Geq
        } else {
          if (strict) picasso.math.hol.Lt
          else picasso.math.hol.Leq
        }
        picasso.math.hol.Application(fct, List(apply(_new), apply(_old)))
    }
  }
  
  def apply(c: Condition): picasso.math.hol.Formula = c match {
    case Eq(l,r) => picasso.math.hol.Application(picasso.math.hol.Eq, List(apply(l), apply(r)))
    case Lt(l,r) => picasso.math.hol.Application(picasso.math.hol.Lt, List(apply(l), apply(r)))
    case Leq(l,r) => picasso.math.hol.Application(picasso.math.hol.Leq, List(apply(l), apply(r)))
    case And(l,r) => picasso.math.hol.Application(picasso.math.hol.And, List(apply(l), apply(r)))
    case Or(l,r) => picasso.math.hol.Application(picasso.math.hol.Or, List(apply(l), apply(r)))
    case Not(c) => picasso.math.hol.Application(picasso.math.hol.Not, List(apply(c)))
    case Literal(l) => picasso.math.hol.Literal(l).setType(picasso.math.hol.Bool)
  }

}

object FromMathAst {

  def variable(v: picasso.math.hol.Variable): Variable = {
    Variable(v.name)
  }

  def expression(f: picasso.math.hol.Formula): Expression = f match {
    case picasso.math.hol.Application(fct, args) =>
      val args2 = args map expression
      fct match {
        case picasso.math.hol.Plus => args2.reduceLeft(Plus(_, _))
        case picasso.math.hol.Minus => args2.reduceLeft(Minus(_,_))
        case picasso.math.hol.Times =>
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
    case picasso.math.hol.Literal(l: Int) => Constant(l)
    case picasso.math.hol.Variable(v) => Variable(v)
    case other => Logger.logAndThrow("integer.MathAst", LogError, "FromMathAst.expression: " + other)
  }

  protected def inEq(greater: Boolean, strict: Boolean, args: List[picasso.math.hol.Formula]): Condition = {
    Logger.assert( args.size == 2, "integer.MathAst", "FromMathAst, inEq with " + args )
    val a1 = expression(args(0))
    val a2 = expression(args(1))
    val (small,big) = if (greater) (a2, a1) else (a1, a2)
    if (strict) Lt(small, big) else Leq(small, big)
  }

  def apply(f: picasso.math.hol.Formula): Condition = f match {
    case picasso.math.hol.Application(fct, args) =>
      fct match {
        case picasso.math.hol.And => (args.iterator map apply).reduceLeft(And(_, _))
        case picasso.math.hol.Or =>  (args.iterator map apply).reduceLeft(Or(_, _))
        case picasso.math.hol.Not => 
          Logger.assert( args.size == 1, "integer.MathAst",
            "FromMathAst, Not with " + args )
          Not(apply(args(0)))
        case picasso.math.hol.Implies => 
          Logger.assert( args.size == 2, "integer.MathAst",
            "FromMathAst, Implies with " + args )
          Or(Not(apply(args(0))), apply(args(1)))

        case picasso.math.hol.Eq =>
          Logger.assert( args.size == 2, "integer.MathAst",
            "FromMathAst, Eq with " + args )
          Eq(expression(args(0)), expression(args(1)))
        case picasso.math.hol.Neq => 
          Logger.assert( args.size == 2, "integer.MathAst",
            "FromMathAst, Neq with " + args )
          Not(Eq(expression(args(0)), expression(args(1))))
        case picasso.math.hol.Geq => inEq(true, false, args)
        case picasso.math.hol.Leq => inEq(false, false, args)
        case picasso.math.hol.Gt => inEq(true, true, args)
        case picasso.math.hol.Lt => inEq(false, true, args)
        case other => Logger.logAndThrow("integer.MathAst", LogError, "FromMathAst fct: " + other)
      }
    case picasso.math.hol.Literal(l: Boolean) => Literal(l)
    case other => Logger.logAndThrow("integer.MathAst", LogError, "FromMathAst: " + other)
  }

}
