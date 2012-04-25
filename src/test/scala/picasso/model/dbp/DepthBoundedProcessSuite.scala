package picasso.model.dbp

import org.scalatest._
import picasso.math.WellPartialOrdering._
import picasso.analysis._
import picasso.utils.{LogDebug, LogNotice, LogInfo, Logger}
//import parma_polyhedra_library._


class DepthBoundedProcessSuite extends FunSuite {
 
  abstract class Loc
  case object A extends Loc
  case object B extends Loc
  case object C extends Loc
  case object D extends Loc

  implicit val locWPO = IdentityWPO[Loc]

  trait LocDBCT extends DBCT {
    type State = Loc
    type EL = Unit
  }
  
  //val _ = System.loadLibrary("ppl_java")

  val emp = DepthBoundedConf.empty[LocDBCT]
  def mkA = Thread[Loc](A,0)
  def mkB = Thread[Loc](B,0)
  def mkC = Thread[Loc](C,0)
  def mkD = Thread[Loc](D,0)
  val a0 = mkA
  val b0 = mkB
  val c0 = mkC
  val d0 = mkD
  val b1 = b0++
  val c1 = c0++
  val c2 = c1++
  val cc0 = mkC
  val cc1 = cc0++

/*
  test("testing polyhedra library") {
    System.loadLibrary("ppl_java")
    
    Parma_Polyhedra_Library.initialize_library

    val x1 = new Variable(0)
    val x2 = new Variable(1)
    val le_0 = new Linear_Expression_Coefficient(new Coefficient(0))

    val le_x1 = new Linear_Expression_Variable(x1)
    val le_x2 = new Linear_Expression_Variable(x2)
    val c = new Constraint(le_x1 subtract le_x2, Relation_Symbol.EQUAL, le_0)
    val oct = new Octagonal_Shape_mpz_class(2, Degenerate_Element.UNIVERSE)
    oct add_constraint c
    val oct2 = new Octagonal_Shape_mpz_class(oct)
    oct concatenate_assign oct
    oct2.expand_space_dimension(x1, 1)
    //println(oct)
    //println(oct2)
    Parma_Polyhedra_Library.finalize_library
  }
*/

  test("post computation") {
    // a simple transition simulating async sending of a message 
    val tr1 = { 
      val preCond = emp ++ (a0 --> b0)
      val postCond = preCond ++ (b0 --> c0)
      val mapping = Map(a0 -> a0, b0 -> b0)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping)
    }
    val pre1 = emp ++ (a0 --> b1)
    val postSet1 = tr1(pre1)
    assert(postSet1.size == 1)
    val post1 = postSet1.head
    val post1Expected = emp ++ (a0 --> b1) ++ (a0 --> b0) ++ (b0 --> c0)
    assert(post1 isSubgraphOf post1Expected)
    assert(post1Expected isSubgraphOf post1)


    // a simple transition simulating a message reception + local transition
    val tr2 = { 
      val preCond = emp ++ (b0 --> c0)
      val postCond = emp + d0
      val mapping = Map(b0 -> d0)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping)
    }
    val postSet2 = tr2(post1)
    assert(postSet2.size == 1)
    val post2 = postSet2.head
    val post2Expected = emp ++ (a0 --> b1) ++ (a0 --> d0)
    assert(post2 isSubgraphOf post2Expected)
    assert(post2Expected isSubgraphOf post2)

    // check dangling edge removal
    val pre3 = emp ++ (a0 --> c0) ++ (c0 --> b0)
    val tr3 = {
      val preCond = emp ++ (a0 --> c0)
      val postCond = emp + d0
      val mapping = Map(a0 -> d0)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping)
    }
    val postSet3 = tr3(pre3)
    assert(postSet3.size == 1)
    val post3 = postSet3.head
    val post3Expected = emp + d0 + b0
    assert(post3 isSubgraphOf post3Expected)
    assert(post3Expected isSubgraphOf post3)

    // check inhibitors and monotonicity abstraction
    val pre4 = emp ++ (a0 --> c0) ++ (a0 --> b0) ++ (a0 --> b1)
    val tr4 = {
      val preCond = emp + a0
      val postCond = emp + d0
      val mapping = Map(a0 -> d0)
      val inhibitor = emp ++ (a0 --> b0)
      val inhibitorMap = Map(a0 -> a0)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping, Map(), Some((inhibitor, inhibitorMap)))
    }
    val postSet4 = tr4(pre4)
    assert(postSet4.size == 1)
    val post4 = postSet4.head
    val post4Expected = emp ++ (d0 --> c0)
    assert(post4 isSubgraphOf post4Expected)
    assert(post4Expected isSubgraphOf post4)

    //
    val pre5 = emp ++ (a0 --> c0) ++ (a0 --> b0)
    val tr5 = {
      val preCond = emp ++ (a0 --> c0)
      val postCond = emp + d0
      val mapping = Map(a0 -> d0)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping)
    }
    val postSet5 = tr5(pre5)
    assert(postSet5.size == 1)
    val post5 = postSet5.head
    val post5Expected = emp ++ (d0 --> b0)
    assert(post5 isSubgraphOf post5Expected)
    assert(post5Expected isSubgraphOf post5)
  }

  /*
  test("forward covering test") {
    //Logger.defaultLogger.setMinPriority(LogDebug)
    val trans1 = {
      val preCond = emp + a0
      val postCond = preCond ++ (b0 --> a0) ++ (a0 --> b0)
      val mapping = Map(a0 -> a0)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping)
    }

    val trans2 = {
      val preCond = emp ++ (b0 --> a0)
      val postCond = preCond ++ (a0 --> c0) ++ (c0 --> b0)
      val mapping = Map(a0 -> a0, b0 -> b0)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping)
    }
    
    val proc1 = new DepthBoundedProcess[LocDBCT](List(trans1, trans2)) with SimpleForward
    val init = emp + a0
    val target = emp + d0

    assert(!proc1.forwardCoveringWithTrace(init, target).isDefined)

    Logger("TEST", LogNotice, "forward")

    val c01 = Thread[Loc](C,0)
 
    val trans3 = {
      val preCond = emp + c0 + c01
      val postCond = preCond + d0
      val mapping = Map(c0 -> c0, c01 -> c01)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping)
    }

    val proc2 = new DepthBoundedProcess[LocDBCT](List(trans1, trans2, trans3)) with SimpleForward
    
    assert(proc2.forwardCoveringWithTrace(init, target).isDefined)

    val trans4 = {
      val preCond = emp ++ (a0 --> c0)
      val postCond = emp + d0
      val mapping = Map(a0 -> d0)
      DepthBoundedTransition[LocDBCT]("t", preCond, postCond, mapping)
    }

    val proc3 = new DepthBoundedProcess[LocDBCT](List(trans1, trans2, trans4)) with SimpleForward
    
    assert(proc3.forwardCoveringWithTrace(init, target).isDefined)
  }*/

  test("widening test with height more than ω²") {
    // client-server example: one server, many clients, many message per client.
    val proc = new DepthBoundedProcess[LocDBCT](Nil) with SimpleForward
    val c2 = c1++
    val fullCover = emp ++ (b1 --> a0) ++ (c2 --> b1)

    val start = emp ++ (b1 --> a0)
    var cover = start
    val maxStep = 5
    for (i <- 1 to maxStep) {
      var adding = emp ++ (b0 --> a0)
      for (j <- 0 until i) adding = adding ++ (mkC --> b0)
      val pred = cover
      val next = (pred ++ adding)
      cover = proc.widening(pred, next)
      cover = proc.widening(pred, cover)
      Logger("TEST", LogNotice, "∇: from " + pred + " with " + next + " to " + cover)
    }
    Logger("TEST", LogNotice, "folded cover: " + cover.fold)
    assert(cover isSubgraphOf fullCover, "full cover: " + fullCover)
    assert(fullCover isSubgraphOf cover, "cover: " + cover)
  }



}

