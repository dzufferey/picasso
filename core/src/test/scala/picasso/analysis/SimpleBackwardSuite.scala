package picasso.analysis

import picasso.model.pn._

import org.scalatest._

class SimpleBackwardSuite extends FunSuite {

  val pn1 = {
    //4 places: p0,p1,p2,p3
    //3 transitions: p0,p1 -> p2, p2 -> p3,p0, p3 -> p1,p2
    val t0 = new PNTransition(List((0,1),(1,1)), List((2,1)))
    val t1 = new PNTransition(List((2,1)), List((3,1),(0,1)))
    val t2 = new PNTransition(List((3,1)), List((1,1),(2,1)))
    new PetriNet(List(t0,t1,t2)) with SimpleBackward
  }
  val init1 = new PNState(Array(2,1,1,0))
  val init2 = new PNState(Array(1,0,0,0))
  val target = new PNState(Array(0,0,10,10))
  
  test("trivial backward for Petri Net") {
    assert(pn1.backwardCovering(init1, target))
    assert(!pn1.backwardCovering(init2, target))
  }
  
  test("trivial backward with trace for Petri Net") {
    val trace1 = pn1.backwardCoveringWithTrace(init1, target)
    assert(trace1.isDefined)
    assert(pn1 isTraceValid trace1.get)
    assert(! pn1.backwardCoveringWithTrace(init2, target).isDefined)
  }

  test("TODO more backward analysis tests") {
    pending
  }

}
