package picasso.analysis

import picasso.model.{PetriNet, PNTransition, PNState}

import org.scalatest._

class SimpleForwardSuite extends FunSuite {

  val pn1 = {
    //4 places: p0,p1,p2,p3
    //3 transitions: p0,p1 -> p2, p2 -> p3,p0, p3 -> p1,p2
    val t0 = new PNTransition(List((0,1),(1,1)), List((2,1)))
    val t1 = new PNTransition(List((2,1)), List((3,1),(0,1)))
    val t2 = new PNTransition(List((3,1)), List((1,1),(2,1)))
    new PetriNet(List(t0,t1,t2)) with SimpleForward
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

  test("TODO more tests") {
    pending
  }

}
