package picasso.model.integer

import org.scalatest._

class ProgramSuite extends FunSuite {

  val v1 = Variable("v1")
  val v2 = Variable("v2")
  val v3 = Variable("v3")
  val v4 = Variable("v4")
  val v5 = Variable("v5")
  val v6 = Variable("v6")

  val c0 = Constant(0)
  val c1 = Constant(1)

  test("test ranking fct candidates generation"){
    //we are interested in the termination of t2^n; t3; t1^(n-1)
    //candidate needed by this loop: X3, but if we change the order or relax #t1, we need X1 + X2 + X3
    // X_1_prime = X_1 + (X_2 + n - 1) - (n - 1),
    // X_2_prime = 0,
    // X_3_prime = X_3 - n + (n - 1),
    // X_4_prime = n - 1,
    // X_5_prime = X_5 + (X4 + n - 1) - (n - 1),
    // X_6_prime = X_6 + 1
    //TODO narrow the #candiates and still get X1 + X2 + X3 ?

    // unfolding; morphing, client: Op2 Fail; folding; covering
    // 1 =< X_1,
    // 0 =< X_2,
    // 0 =< X_3,
    // 0 =< X_4,
    // 1 =< X_5,
    // 1 =< X_6,
    // X_1_prime = X_1 - 1,
    // X_2_prime = X_2,
    // X_3_prime = X_3 + 1,
    // X_4_prime = X_4 + 1,
    // X_5_prime = X_5 - 1
    // X_6_prime = X_6,
    val g1 = And(And(And(And(And(Leq(c1, v1), Leq(c0, v2)), Leq(c0, v3)), Leq(c0, v4)), Leq(c1, v5)), Leq(c1, v6))
    val u1 = Seq(Relation(v1, Minus(v1, c1)), Relation(v2, v2), Relation(v3, Plus(v3, c1)), Relation(v4, Plus(v4, c1)), Relation(v5, Minus(v5, c1)), Relation(v6, v6))
    val t1 = new Transition("1", "1", g1, u1, "t1")

    // unfolding; morphing, client: Op1 -> Op2; folding; covering
    // 0 =< X_1,
    // 0 =< X_2,
    // 1 =< X_3,
    // 0 =< X_4,
    // 0 =< X_5,
    // 0 =< X_6,
    // X_1_prime = X_1,
    // X_2_prime = X_2 + 1,
    // X_3_prime = X_3 - 1,
    // X_4_prime = X_4 + 1,
    // X_5_prime = X_5,
    // X_6_prime = X_6
    val g2 = And(And(And(And(And(Leq(c0, v1), Leq(c0, v2)), Leq(c1, v3)), Leq(c0, v4)), Leq(c0, v5)), Leq(c0, v6))
    val u2 = Seq(Relation(v1, v1), Relation(v2, Plus(v2, c1)), Relation(v3, Minus(v3, c1)), Relation(v4, Plus(v4, c1)), Relation(v5, v5), Relation(v6, v6))
    val t2 = new Transition("1", "1", g2, u2, "t2")

    // unfolding; morphing, client: Op2 Success; folding; covering
    // 0 =< X_1,
    // 1 =< X_2,
    // 0 =< X_3,
    // 1 =< X_4,
    // 0 =< X_5,
    // 0 =< X_6,
    // X_1_prime = X_1 + X_2 - 1,
    // X_2_prime = 0,
    // X_3_prime = X_3
    // X_4_prime = 0,
    // X_5_prime = X_4 + X_5 - 1,
    // X_6_prime = X_6 + 1,
    val g3 = And(And(And(And(And(Leq(c0, v1), Leq(c1, v2)), Leq(c0, v3)), Leq(c1, v4)), Leq(c0, v5)), Leq(c0, v6))
    val u3 = Seq(Relation(v1, Minus(Plus(v1, v2), c1)), Relation(v2, c0), Relation(v3, v3), Relation(v4, c0), Relation(v5, Minus(Plus(v4, v5), c1)), Relation(v6, Plus(v6, c1)))
    val t3 = new Transition("1", "1", g3, u3, "t3")

    val p = new Program("1", List(t1,t2,t3))

    val trs_pred = p.transitionPredicates

    println("Transition Predicates:")
    println(trs_pred.mkString("\n"))

    //sys.error("TODO")

  }



}
