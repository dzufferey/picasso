package picasso.frontend.pi

import org.scalatest._

class PiSuite extends FunSuite {

//from the prolog implementation: 

  val s1 = //scheduler1[S, T1, T2, T3, T4]
    Choice(List(
      Output("T1", List("S"), ProcessID("scheduler2", List("S","T1","T2","T3","T4"))),
      Output("T2", List("S"), ProcessID("scheduler2", List("S","T1","T2","T3","T4"))),
      Output("T3", List("S"), ProcessID("scheduler2", List("S","T1","T2","T3","T4"))),
      Output("T4", List("S"), ProcessID("scheduler2", List("S","T1","T2","T3","T4")))
    ))
  val s2 = Input("S", Nil, ProcessID("scheduler1", List("S","T1","T2","T3","T4"))) //scheduler2[S, T1, T2, T3, T4]
  val m1 = Output("P", Nil, Zero) //simple message[P]
  val m2 = Output("P", List("Reply"), Zero) //message with reply channel[P, Reply]
  val p1 = //place1 [P, PGet, PSnd, PRst]
    Choice(List(
      Input("PGet", List("Reply"), ProcessID("place2", List("P", "PGet", "PSnd", "PRst", "Reply"))),
      Input("PSnd", List("Reply"), Composition(List(ProcessID("msg",List("P")),ProcessID("place3", List("P", "PGet", "PSnd", "PRst", "Reply"))))),
      Input("PRst", List("Reply"), Restriction("PP", ProcessID("place3", List("PP", "PGet", "PSnd", "PRst", "Reply"))))
    ))
  val p2 = Input("P", List(), ProcessID("place3", List("P", "PGet", "PSnd", "PRst", "Reply")))//place2 [P, PGet, PSnd, PRst, Reply]
  val p3 = Output("Reply", Nil, ProcessID("place1", List("P", "PGet", "PSnd", "PRst")))//place3 [P, PGet, PSnd, PRst, Reply]
  val t11 = Input("T1", List("S"), ProcessID("t1_2", List("T1", "S", "P1", "P2Get", "P4Snd"))) //ProcessID("t1_1", List(T1, P1, P2Get, P4Snd))
  val t12 = Input("P1", List(), ProcessID("t1_3", List("T1", "S", "P1", "P2Get", "P4Snd")))  //ProcessID("t1_2", List(T1, S, P1, P2Get, P4Snd))
  val t13 = Output("P2Get", List("T1"), ProcessID("t1_4", List("T1", "S", "P1", "P2Get", "P4Snd"))) //ProcessID("t1_3", List(T1, S, P1, P2Get, P4Snd))
  val t14 = //ProcessID("t1_4", List(T1, S, P1, P2Get, P4Snd))
    Input("T1", List(), Composition(List(
      ProcessID("msg", List("P1")),
      ProcessID("msg_sending", List("T1", "P4Snd")),
      ProcessID("t1_5", List("T1", "S", "P1", "P2Get", "P4Snd"))
    )))
  val t15 = Input("T1", List(), ProcessID("t1_6", List("T1", "S", "P1", "P2Get", "P4Snd"))) //ProcessID("t1_5", List(T1, S, P1, P2Get, P4Snd))
  val t16 = Output("S", List(), ProcessID("t1_1", List("T1", "P1", "P2Get", "P4Snd"))) //ProcessID("t1_6", List(T1, S, P1, P2Get, P4Snd))
  val t21 = Input("T2", List("S"), ProcessID("t2_2", List("T2", "S", "P1", "P2Rst", "P3"))) //ProcessID("t2_1", List(T2, P1, P2Rst, P3))
  val t22 = Input("P1", List(), ProcessID("t2_3", List("T2", "S", "P1", "P2Rst", "P3"))) //ProcessID("t2_2", List(T2, S, P1, P2Rst, P3))
  val t23 = Output("P2Rst", List("T2"), ProcessID("t2_4", List("T2", "S", "P1", "P2Rst", "P3"))) //ProcessID("t2_3", List(T2, S, P1, P2Rst, P3))
  val t24 = //ProcessID("t2_4", List(T2, S, P1, P2Rst, P3))
    Input("T2", List(), Composition(List(
      ProcessID("msg", List("P3")),
      ProcessID("t2_5", List("T2", "S", "P1", "P2Rst", "P3"))
    )))
  val t25 = Output("S", List(), ProcessID("t2_1", List("T2", "P1", "P2Rst", "P3"))) //ProcessID("t2_5", List(T2, S, P1, P2Rst, P3))
  val t31 = Input("T3", List("S"), ProcessID("t3_2", List("T3", "S", "P2Snd", "P3", "P4Get"))) //ProcessID("t3_1", List(T3, P2Snd, P3, P4Get))
  val t32 = Input("P3", List(), ProcessID("t3_3", List("T3", "S", "P2Snd", "P3", "P4Get"))) //ProcessID("t3_2", List(T3, S, P2Snd, P3, P4Get))
  val t33 = Output("P4Get", List("T3"), ProcessID("t3_4", List("T3", "S", "P2Snd", "P3", "P4Get"))) //ProcessID("t3_3", List(T3, S, P2Snd, P3, P4Get))
  val t34 = Input("T3", List(), ProcessID("t3_5", List("T3", "S", "P2Snd", "P3", "P4Get"))) //ProcessID("t3_4", List(T3, S, P2Snd, P3, P4Get))
  val t35 = //ProcessID("t3_5", List(T3, S, P2Snd, P3, P4Get)
    Output("P2Snd", List("T3"), Composition(List(
      ProcessID("msg", List("P3")),
      ProcessID("t3_6", List("T3", "S", "P2Snd", "P3", "P4Get"))
    )))
  val t36 = Input("T3", List(), ProcessID("t3_8", List("T3", "S", "P2Snd", "P3", "P4Get"))) //ProcessID("t3_6", List(T3, S, P2Snd, P3, P4Get))
  val t37 = Output("S", List(), ProcessID("t3_1", List("T3", "P2Snd", "P3", "P4Get"))) //ProcessID("t3_8", List(T3, S, P2Snd, P3, P4Get))
  val t41 = Input("T4", List("S"), ProcessID("t4_2", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))) //ProcessID("t4_1", List(T4, P1, P2Snd, P3, P4Rst))
  val t42 = Input("P3", List(), ProcessID("t4_3", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))) //ProcessID("t4_2", List(T4, S, P1, P2Snd, P3, P4Rst))
  val t43 = Output("P4Rst", List("T4"), ProcessID("t4_4", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))) //ProcessID("t4_3", List(T4, S, P1, P2Snd, P3, P4Rst))
  val t44 = //ProcessID("t4_4", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
    Input("T4", List(), Composition(List(
      ProcessID("msg", List("P1")),
      ProcessID("msg_sending", List("T4", "P2Snd")),
      ProcessID("t4_5", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))
    )))
  val t45 = Input("T4", List(), ProcessID("t4_8", List("T4", "S", "P1", "P2Snd", "P3", "P4Rst"))) //ProcessID("t4_5", List(T4, S, P1, P2Snd, P3, P4Rst))
  val t46 = Output("S", List(), ProcessID("t4_1", List("T4", "P1", "P2Snd", "P3", "P4Rst"))) //ProcessID("t4_8", List(T4, S, P1, P2Snd, P3, P4Rst))

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
        Input("PGet", List("Other"), ProcessID("place2", List("P", "PGet", "PSnd", "PRst", "Other"))),
        Input("PSnd", List("Other"), Composition(List(ProcessID("msg",List("P")),ProcessID("place3", List("P", "PGet", "PSnd", "PRst", "Other"))))),
        Input("PRst", List("Other"), Restriction("PP", ProcessID("place3", List("PP", "PGet", "PSnd", "PRst", "Other"))))
      ))
    val m22 = Output("P", List("Other"), Zero)
    assert((p1 alphaAll subst2) == p12)
    assert((t11 alphaAll subst2) == t11)
    assert((m2 alphaAll subst2) == m22)
    
    val p13 =
      Choice(List(
        Input("PGet", List("Reply"), ProcessID("place2", List("Reply", "PGet", "PSnd", "PRst", "Reply"))),
        Input("PSnd", List("Reply"), Composition(List(ProcessID("msg",List("Reply")),ProcessID("place3", List("Reply", "PGet", "PSnd", "PRst", "Reply"))))),
        Input("PRst", List("Reply"), Restriction("PP", ProcessID("place3", List("PP", "PGet", "PSnd", "PRst", "Reply"))))
      ))
    val m23 = Output("Reply", List("Reply"), Zero)
    assert((p1 alphaAll subst3) == p13)
    assert((t11 alphaAll subst3) == t11)
    assert((m2 alphaAll subst3) == m23)
    
    val p14 =
      Choice(List(
        Input("PGet", List("Reply"), ProcessID("place2", List("P", "PGet", "PSnd", "PRst", "Reply"))),
        Input("PSnd", List("Reply"), Composition(List(ProcessID("msg",List("P")),ProcessID("place3", List("P", "PGet", "PSnd", "PRst", "Reply"))))),
        Input("PRst", List("Reply"), Restriction("Not", ProcessID("place3", List("Not", "PGet", "PSnd", "PRst", "Reply"))))
      ))
    val t114 = Input("T1", List("Not"), ProcessID("t1_2", List("T1", "Not", "P1", "P2Get", "P4Snd")))
    assert((p1 alphaAll subst4) == p14)
    assert((t11 alphaAll subst4) == t114)
    assert((m2 alphaAll subst4) == m2)
  }

  test("alpha unsafe") {
    assert((p1 alphaUnsafe subst1) == p1)
    assert((t11 alphaUnsafe subst1) == t11)
    assert((m2 alphaUnsafe subst1) == m2)

    val m22 = Output("P", List("Other"), Zero)
    assert((p1 alphaUnsafe subst2) == p1)
    assert((t11 alphaUnsafe subst2) == t11)
    assert((m2 alphaUnsafe subst2) == m22)
    
    val p13 =
      Choice(List(
        Input("PGet", List("Reply"), ProcessID("place2", List("Reply", "PGet", "PSnd", "PRst", "Reply"))),
        Input("PSnd", List("Reply"), Composition(List(ProcessID("msg",List("Reply")),ProcessID("place3", List("Reply", "PGet", "PSnd", "PRst", "Reply"))))),
        Input("PRst", List("Reply"), Restriction("PP", ProcessID("place3", List("PP", "PGet", "PSnd", "PRst", "Reply"))))
      ))
    val m23 = Output("Reply", List("Reply"), Zero)
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

    val m22 = Output("P", List("Other"), Zero)
    assert((p1 alpha subst2) == p1)
    assert((t11 alpha subst2) == t11)
    assert((m2 alpha subst2) == m22)
    
    val captured = (new picasso.utils.AlphaIterator).next
    val p13 =
      Choice(List(
        Input("PGet", List(captured), ProcessID("place2", List("Reply", "PGet", "PSnd", "PRst", captured))),
        Input("PSnd", List(captured), Composition(List(ProcessID("msg",List("Reply")),ProcessID("place3", List("Reply", "PGet", "PSnd", "PRst", captured))))),
        Input("PRst", List(captured), Restriction("PP", ProcessID("place3", List("PP", "PGet", "PSnd", "PRst", captured))))
      ))
    val m23 = Output("Reply", List("Reply"), Zero)
    assert((p1 alpha subst3) == p13)
    assert((t11 alpha subst3) == t11)
    assert((m2 alpha subst3) == m23)
    
    assert((p1 alpha subst4) == p1)
    assert((t11 alpha subst4) == t11)
    assert((m2 alpha subst4) == m2)

    //TODO more tests
  }
  
  test("is observable prefix") {
    val a = Input("A", Nil, Input("B", Nil, Zero))
    assert(a isObservablePrefix "A")
    assert(!(a isObservablePrefix "B"))
    val b = Output("C", Nil, Output("D", Nil, Zero))
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
