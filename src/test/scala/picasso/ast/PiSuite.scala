package picasso.ast

import org.scalatest._

class PiSuite extends FunSuite {

//from the prolog implementation: 

  val s1 = //scheduler1[S, T1, T2, T3, T4]
    Choice(List(
      OutputPrefix("T1", List("S"), PiProcessID("scheduler2", List("S","T1","T2","T3","T4"))),
      OutputPrefix("T2", List("S"), PiProcessID("scheduler2", List("S","T1","T2","T3","T4"))),
      OutputPrefix("T3", List("S"), PiProcessID("scheduler2", List("S","T1","T2","T3","T4"))),
      OutputPrefix("T4", List("S"), PiProcessID("scheduler2", List("S","T1","T2","T3","T4")))
    ))
  val s2 = InputPrefix("S", Nil, PiProcessID("scheduler1", List("S","T1","T2","T3","T4"))) //scheduler2[S, T1, T2, T3, T4]
  val m1 = OutputPrefix("P", Nil, PiZero) //simple message[P]
  val m2 = OutputPrefix("P", List("Reply"), PiZero) //message with reply channel[P, Reply]
  val p1 = //place1 [P, PGet, PSnd, PRst]
    Choice(List(
      InputPrefix("PGet", List("Reply"), PiProcessID("place2", List("P", "PGet", "PSnd", "PRst", "Reply"))),
      InputPrefix("PSnd", List("Reply"), Composition(List(PiProcessID("msg",List("P")),PiProcessID("place3", List("P", "PGet", "PSnd", "PRst", "Reply"))))),
      InputPrefix("PRst", List("Reply"), Restriction("PP", PiProcessID("place3", List("PP", "PGet", "PSnd", "PRst", "Reply"))))
    ))
  val p2 = InputPrefix("P", List(), PiProcessID("place3", List("P", "PGet", "PSnd", "PRst", "Reply")))//place2 [P, PGet, PSnd, PRst, Reply]
  val p3 = OutputPrefix("Reply", Nil, PiProcessID("place1", List("P", "PGet", "PSnd", "PRst")))//place3 [P, PGet, PSnd, PRst, Reply]
  val t11 = InputPrefix("T1", List("S"), PiProcessID("t1_2", List("T1", "S", "P1", "P2Get", "P4Snd"))) //PiProcessID("t1_1", List(T1, P1, P2Get, P4Snd))
  val t12 = InputPrefix("P1", List(), PiProcessID("t1_3", List("T1", "S", "P1", "P2Get", "P4Snd")))  //PiProcessID("t1_2", List(T1, S, P1, P2Get, P4Snd))
  val t13 = OutputPrefix("P2Get", List("T1"), PiProcessID("t1_4", List("T1", "S", "P1", "P2Get", "P4Snd"))) //PiProcessID("t1_3", List(T1, S, P1, P2Get, P4Snd))
  val t14 = //PiProcessID("t1_4", List(T1, S, P1, P2Get, P4Snd))
    InputPrefix("T1", List(), Composition(List(
      PiProcessID("msg", List("P1")),
      PiProcessID("msg_sending", List("T1", "P4Snd")),
      PiProcessID("t1_5", List("T1", "S", "P1", "P2Get", "P4Snd"))
    )))
  val t15 = InputPrefix("T1", List(), PiProcessID("t1_6", List("T1", "S", "P1", "P2Get", "P4Snd"))) //PiProcessID("t1_5", List(T1, S, P1, P2Get, P4Snd))
  val t16 = OutputPrefix("S", List(), PiProcessID("t1_1", List("T1", "P1", "P2Get", "P4Snd"))) //PiProcessID("t1_6", List(T1, S, P1, P2Get, P4Snd))
  val t21 = InputPrefix("T2", List("S"), PiProcessID("t2_2", List("T2", "S", "P1", "P2Rst", "P3"))) //PiProcessID("t2_1", List(T2, P1, P2Rst, P3))
  val t22 = InputPrefix("P1", List(), PiProcessID("t2_3", List("T2", "S", "P1", "P2Rst", "P3"))) //PiProcessID("t2_2", List(T2, S, P1, P2Rst, P3))
  val t23 = OutputPrefix("P2Rst", List("T2"), PiProcessID("t2_4", List("T2", "S", "P1", "P2Rst", "P3"))) //PiProcessID("t2_3", List(T2, S, P1, P2Rst, P3))
  val t24 = //PiProcessID("t2_4", List(T2, S, P1, P2Rst, P3))
    InputPrefix("T2", List(), Composition(List(
      PiProcessID("msg", List("P3")),
      PiProcessID("t2_5", List("T2", "S", "P1", "P2Rst", "P3"))
    )))
  val t25 = OutputPrefix("S", List(), PiProcessID("t2_1", List("T2", "P1", "P2Rst", "P3"))) //PiProcessID("t2_5", List(T2, S, P1, P2Rst, P3))
  val t31 = InputPrefix("T3", List("S"), PiProcessID("t3_2", List("T3", "S", "P2Snd", "P3", "P4Get"))) //PiProcessID("t3_1", List(T3, P2Snd, P3, P4Get))
  val t32 = InputPrefix("P3", List(), PiProcessID("t3_3", List("T3", "S", "P2Snd", "P3", "P4Get"))) //PiProcessID("t3_2", List(T3, S, P2Snd, P3, P4Get))
  val t33 = OutputPrefix("P4Get", List("T3"), PiProcessID("t3_4", List("T3", "S", "P2Snd", "P3", "P4Get"))) //PiProcessID("t3_3", List(T3, S, P2Snd, P3, P4Get))
  val t34 = InputPrefix("T3", List(), PiProcessID("t3_5", List("T3", "S", "P2Snd", "P3", "P4Get"))) //PiProcessID("t3_4", List(T3, S, P2Snd, P3, P4Get))
  val t35 = //PiProcessID("t3_5", List(T3, S, P2Snd, P3, P4Get)
    OutputPrefix("P2Snd", List("T3"), Composition(List(
      PiProcessID("msg", List("P3")),
      PiProcessID("t3_6", List("T3", "S", "P2Snd", "P3", "P4Get"))
    )))
  val t36 = InputPrefix("T3", List(), PiProcessID("t3_8", List("T3", "S", "P2Snd", "P3", "P4Get"))) //PiProcessID("t3_6", List(T3, S, P2Snd, P3, P4Get))
  val t37 = OutputPrefix("S", List(), PiProcessID("t3_1", List("T3", "P2Snd", "P3", "P4Get"))) //PiProcessID("t3_8", List(T3, S, P2Snd, P3, P4Get))
  val t41 = InputPrefix("T4", List("S"), PiProcessID("t4_2", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))) //PiProcessID("t4_1", List(T4, P1, P2Snd, P3, P4Rst))
  val t42 = InputPrefix("P3", List(), PiProcessID("t4_3", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))) //PiProcessID("t4_2", List(T4, S, P1, P2Snd, P3, P4Rst))
  val t43 = OutputPrefix("P4Rst", List("T4"), PiProcessID("t4_4", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))) //PiProcessID("t4_3", List(T4, S, P1, P2Snd, P3, P4Rst))
  val t44 = //PiProcessID("t4_4", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
    InputPrefix("T4", List(), Composition(List(
      PiProcessID("msg", List("P1")),
      PiProcessID("msg_sending", List("T4", "P2Snd")),
      PiProcessID("t4_5", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
    )))
  val t45 = InputPrefix("T4", List(), PiProcessID("t4_8", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))) //PiProcessID("t4_5", List(T4, S, P1, P2Snd, P3, P4Rst))
  val t46 = OutputPrefix("S", List(), PiProcessID("t4_1", List("T4", "P1", "P2Snd", "P3", "P4Rst"))) //PiProcessID("t4_8", List(T4, S, P1, P2Snd, P3, P4Rst))

  test("free names"){
    assert(s1.freeNames == Set("T1","T2","T3","T4","S"))
    assert(s2.freeNames == Set("T1","T2","T3","T4","S"))
    assert(m1.freeNames == Set("P"))
    assert(m2.freeNames == Set("P", "Reply"))
    assert(p1.freeNames == Set("P", "PGet", "PSnd", "PRst")) //PP is not free
    assert(p2.freeNames == Set("P", "PGet", "PSnd", "PRst", "Reply"))
    assert(p3.freeNames == Set("P", "PGet", "PSnd", "PRst", "Reply"))
    assert(t11.freeNames == Set("T1", "P1", "P2Get", "P4Snd")) //S is not free
    assert(t12.freeNames == Set("S", "T1", "P1", "P2Get", "P4Snd"))
    assert(t13.freeNames == Set("S", "T1", "P1", "P2Get", "P4Snd"))
    assert(t14.freeNames == Set("S", "T1", "P1", "P2Get", "P4Snd"))
    assert(t15.freeNames == Set("S", "T1", "P1", "P2Get", "P4Snd"))
    assert(t16.freeNames == Set("S", "T1", "P1", "P2Get", "P4Snd"))
    assert(t21.freeNames == Set("T2", "P1", "P2Rst", "P3")) //S is not free
    assert(t22.freeNames == Set("S", "T2", "P1", "P2Rst", "P3"))
    assert(t23.freeNames == Set("S", "T2", "P1", "P2Rst", "P3"))
    assert(t24.freeNames == Set("S", "T2", "P1", "P2Rst", "P3"))
    assert(t25.freeNames == Set("S", "T2", "P1", "P2Rst", "P3"))
    assert(t31.freeNames == Set("T3", "P2Snd", "P3", "P4Get")) //S is not free
    assert(t32.freeNames == Set("S", "T3", "P2Snd", "P3", "P4Get"))
    assert(t33.freeNames == Set("S", "T3", "P2Snd", "P3", "P4Get"))
    assert(t34.freeNames == Set("S", "T3", "P2Snd", "P3", "P4Get"))
    assert(t35.freeNames == Set("S", "T3", "P2Snd", "P3", "P4Get"))
    assert(t36.freeNames == Set("S", "T3", "P2Snd", "P3", "P4Get"))
    assert(t37.freeNames == Set("S", "T3", "P2Snd", "P3", "P4Get"))
    assert(t41.freeNames == Set("T4", "P1", "P2Snd", "P3", "P4Rst"))
    assert(t42.freeNames == Set("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
    assert(t43.freeNames == Set("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
    assert(t44.freeNames == Set("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
    assert(t45.freeNames == Set("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
    assert(t46.freeNames == Set("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
  }
  
  test("bound names"){
    assert(s1.boundNames == Set.empty[String])
    assert(s2.boundNames == Set.empty[String])
    assert(m1.boundNames == Set.empty[String])
    assert(m2.boundNames == Set.empty[String])
    assert(p1.boundNames == Set("PP", "Reply"))
    assert(p2.boundNames == Set.empty[String])
    assert(p3.boundNames == Set.empty[String])
    assert(t11.boundNames == Set("S"))
    assert(t12.boundNames == Set.empty[String])
    assert(t13.boundNames == Set.empty[String])
    assert(t14.boundNames == Set.empty[String])
    assert(t15.boundNames == Set.empty[String])
    assert(t16.boundNames == Set.empty[String])
    assert(t21.boundNames == Set("S"))
    assert(t22.boundNames == Set.empty[String])
    assert(t23.boundNames == Set.empty[String])
    assert(t24.boundNames == Set.empty[String])
    assert(t25.boundNames == Set.empty[String])
    assert(t31.boundNames == Set("S"))
    assert(t32.boundNames == Set.empty[String])
    assert(t33.boundNames == Set.empty[String])
    assert(t34.boundNames == Set.empty[String])
    assert(t35.boundNames == Set.empty[String])
    assert(t36.boundNames == Set.empty[String])
    assert(t37.boundNames == Set.empty[String])
    assert(t41.boundNames == Set("S"))
    assert(t42.boundNames == Set.empty[String])
    assert(t43.boundNames == Set.empty[String])
    assert(t44.boundNames == Set.empty[String])
    assert(t45.boundNames == Set.empty[String])
    assert(t46.boundNames == Set.empty[String])
  }

  val subst1 = scala.collection.immutable.TreeMap.empty[String, String]
  val subst2 = scala.collection.immutable.TreeMap.empty[String, String] + Pair("Reply","Other")
  val subst3 = scala.collection.immutable.TreeMap.empty[String, String] + Pair("P","Reply")
  val subst4 = scala.collection.immutable.TreeMap.empty[String, String] + Pair("S","Not") + Pair("PP", "Not")

  test("alpha all") {
    assert((p1 alphaAll subst1) == p1)
    assert((t11 alphaAll subst1) == t11)
    assert((m2 alphaAll subst1) == m2)

    val p12 =
      Choice(List(
        InputPrefix("PGet", List("Other"), PiProcessID("place2", List("P", "PGet", "PSnd", "PRst", "Other"))),
        InputPrefix("PSnd", List("Other"), Composition(List(PiProcessID("msg",List("P")),PiProcessID("place3", List("P", "PGet", "PSnd", "PRst", "Other"))))),
        InputPrefix("PRst", List("Other"), Restriction("PP", PiProcessID("place3", List("PP", "PGet", "PSnd", "PRst", "Other"))))
      ))
    val m22 = OutputPrefix("P", List("Other"), PiZero)
    assert((p1 alphaAll subst2) == p12)
    assert((t11 alphaAll subst2) == t11)
    assert((m2 alphaAll subst2) == m22)
    
    val p13 =
      Choice(List(
        InputPrefix("PGet", List("Reply"), PiProcessID("place2", List("Reply", "PGet", "PSnd", "PRst", "Reply"))),
        InputPrefix("PSnd", List("Reply"), Composition(List(PiProcessID("msg",List("Reply")),PiProcessID("place3", List("Reply", "PGet", "PSnd", "PRst", "Reply"))))),
        InputPrefix("PRst", List("Reply"), Restriction("PP", PiProcessID("place3", List("PP", "PGet", "PSnd", "PRst", "Reply"))))
      ))
    val m23 = OutputPrefix("Reply", List("Reply"), PiZero)
    assert((p1 alphaAll subst3) == p13)
    assert((t11 alphaAll subst3) == t11)
    assert((m2 alphaAll subst3) == m23)
    
    val p14 =
      Choice(List(
        InputPrefix("PGet", List("Reply"), PiProcessID("place2", List("P", "PGet", "PSnd", "PRst", "Reply"))),
        InputPrefix("PSnd", List("Reply"), Composition(List(PiProcessID("msg",List("P")),PiProcessID("place3", List("P", "PGet", "PSnd", "PRst", "Reply"))))),
        InputPrefix("PRst", List("Reply"), Restriction("Not", PiProcessID("place3", List("Not", "PGet", "PSnd", "PRst", "Reply"))))
      ))
    val t114 = InputPrefix("T1", List("Not"), PiProcessID("t1_2", List("T1", "Not", "P1", "P2Get", "P4Snd")))
    assert((p1 alphaAll subst4) == p14)
    assert((t11 alphaAll subst4) == t114)
    assert((m2 alphaAll subst4) == m2)
  }

  test("alpha unsafe") {
    assert((p1 alphaUnsafe subst1) == p1)
    assert((t11 alphaUnsafe subst1) == t11)
    assert((m2 alphaUnsafe subst1) == m2)

    val m22 = OutputPrefix("P", List("Other"), PiZero)
    assert((p1 alphaUnsafe subst2) == p1)
    assert((t11 alphaUnsafe subst2) == t11)
    assert((m2 alphaUnsafe subst2) == m22)
    
    val p13 =
      Choice(List(
        InputPrefix("PGet", List("Reply"), PiProcessID("place2", List("Reply", "PGet", "PSnd", "PRst", "Reply"))),
        InputPrefix("PSnd", List("Reply"), Composition(List(PiProcessID("msg",List("Reply")),PiProcessID("place3", List("Reply", "PGet", "PSnd", "PRst", "Reply"))))),
        InputPrefix("PRst", List("Reply"), Restriction("PP", PiProcessID("place3", List("PP", "PGet", "PSnd", "PRst", "Reply"))))
      ))
    val m23 = OutputPrefix("Reply", List("Reply"), PiZero)
    assert((p1 alphaUnsafe subst3) == p13)
    assert((t11 alphaUnsafe subst3) == t11)
    assert((m2 alphaUnsafe subst3) == m23)
    
    assert((p1 alphaUnsafe subst4) == p1)
    assert((t11 alphaUnsafe subst4) == t11)
    assert((m2 alphaUnsafe subst4) == m2)
  }

  test("alpha safe") {
    assert((p1 alpha subst1) == p1)
    assert((t11 alpha subst1) == t11)
    assert((m2 alpha subst1) == m2)

    val m22 = OutputPrefix("P", List("Other"), PiZero)
    assert((p1 alpha subst2) == p1)
    assert((t11 alpha subst2) == t11)
    assert((m2 alpha subst2) == m22)
    
    val captured = (new picasso.utils.AlphaIterator).next
    val p13 =
      Choice(List(
        InputPrefix("PGet", List(captured), PiProcessID("place2", List("Reply", "PGet", "PSnd", "PRst", captured))),
        InputPrefix("PSnd", List(captured), Composition(List(PiProcessID("msg",List("Reply")),PiProcessID("place3", List("Reply", "PGet", "PSnd", "PRst", captured))))),
        InputPrefix("PRst", List(captured), Restriction("PP", PiProcessID("place3", List("PP", "PGet", "PSnd", "PRst", captured))))
      ))
    val m23 = OutputPrefix("Reply", List("Reply"), PiZero)
    assert((p1 alpha subst3) == p13)
    assert((t11 alpha subst3) == t11)
    assert((m2 alpha subst3) == m23)
    
    assert((p1 alpha subst4) == p1)
    assert((t11 alpha subst4) == t11)
    assert((m2 alpha subst4) == m2)

    //TODO more tests
  }
  
  test("is observable prefix") {
    val a = InputPrefix("A", Nil, InputPrefix("B", Nil, PiZero))
    assert(a isObservablePrefix "A")
    assert(!(a isObservablePrefix "B"))
    val b = OutputPrefix("C", Nil, OutputPrefix("D", Nil, PiZero))
    assert(b isObservablePrefix "C")
    assert(!(b isObservablePrefix "D"))
    val c = Composition(List(a,b))
    assert(c isObservablePrefix "A")
    assert(!(c isObservablePrefix "B"))
    assert(c isObservablePrefix "C")
    assert(!(c isObservablePrefix "D"))
    val d = Restriction("A", Choice(List(a,b)))
    assert(!(d isObservablePrefix "A"))
    assert(!(d isObservablePrefix "B"))
    assert(d isObservablePrefix "C")
    assert(!(d isObservablePrefix "D"))
  }
}
