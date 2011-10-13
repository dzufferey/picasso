package picasso.analysis

import picasso.model.pn._

import org.scalatest._

class ForwardWithWideningSuite extends FunSuite {

  val pn1 = {
    //4 places: p0,p1,p2,p3
    //3 transitions: p0,p1 -> p2, p2 -> p3,p0, p3 -> p1,p2
    val t0 = new PNTransition(List((0,1),(1,1)), List((2,1)))
    val t1 = new PNTransition(List((2,1)), List((3,1),(0,1)))
    val t2 = new PNTransition(List((3,1)), List((1,1),(2,1)))
    new PetriNet(List(t0,t1,t2)) with ForwardWithWidening
  }
  
  val init1 = new PNState(List(2,1,1,0).toArray)
  val init2 = new PNState(List(1,0,0,0).toArray)
  val target = new PNState(List(0,0,10,10).toArray)

  test("trivial covering test for Petri Net") {
    assert(pn1.forwardCovering(init1, target))
    assert(!pn1.forwardCovering(init2, target))
  }
  
  test("trivial forward covering with trace for Petri Net") {
    val trace1 = pn1.forwardCoveringWithTrace(init1, target)
    assert(trace1.isDefined)
    assert(pn1 isTraceValid trace1.get)
    assert(! pn1.forwardCoveringWithTrace(init2, target).isDefined)
  }
  
  test("trivial forward covering for Petri Net (computing full cover)") {
    val cover1 = pn1.computeCover(init1)
    assert(cover1(target))
    val cover2 = pn1.computeCover(init2)
    assert(!cover2(target))
  }

  //PN used as counterexample for the MCT algorithm
  val mctCex = {
    //7 places: p0,p1,p2,p3,p4,p5,p6
    //8 transitions:
    val t1 = new PNTransition(List((0,1)), List((1,1)))         //  t1: p0 -> p1
    val t2 = new PNTransition(List((1,1)), List((2,1)))         //  t2: p1 -> p2
    val t3 = new PNTransition(List((2,1)), List((3,1)))         //  t3: p2 -> p3
    val t4 = new PNTransition(List((3,1)), List((2,1),(4,1)))   //  t4: p3 -> p2,p4
    val t5 = new PNTransition(List((0,1)), List((5,1)))         //  t5: p0 -> p5
    val t6 = new PNTransition(List((5,1)), List((3,1),(4,2)))   //  t6: p5 -> p3,p4,p4
    val t7 = new PNTransition(List((0,1)), List((6,1)))         //  t7: p0 -> p6
    val t8 = new PNTransition(List((6,1)), List((1,1),(4,1)))   //  t8: p6 -> p1,p4
    new PetriNet(List(t1,t2,t3,t4,t5,t6,t7,t8)) with ForwardWithWidening
  }
  val cexInit = new PNState(Array(1,0,0,0,0,0,0))
  val cexReachable = new PNState(Array(0,0,1,0,999,0,0))
  
  test("MCT cex") {
    val cover = mctCex.computeCover(cexInit)
    assert(cover(cexReachable))
    val trace = mctCex.forwardCoveringWithTrace(cexInit, cexReachable)
    assert(trace.isDefined)
    assert(mctCex isTraceValid trace.get)
  }

  test("TODO more tests") {
    pending
  }

}
