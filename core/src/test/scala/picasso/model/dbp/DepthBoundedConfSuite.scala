package picasso.model.dbp

import org.scalatest._
import picasso.math.WellPartialOrdering._
import picasso.analysis._
import picasso.utils._


class DepthBoundedConfSuite extends FunSuite {

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

  val emp = DepthBoundedConf.empty[LocDBCT]
  def mkA = Thread[Loc](A,0)
  def mkB = Thread[Loc](B,0)
  def mkC = Thread[Loc](C,0)
  def mkD = Thread[Loc](D,0)
  val a0 = mkA
  val b0 = mkB
  val c0 = mkC
  val d0 = mkD
  val a1 = a0++
  val b1 = b0++
  val c1 = c0++
  val a2 = a1++
  val b2 = b1++
  val c2 = c1++
  val cc0 = mkC
  val cc1 = cc0++
  val cc2 = cc1++

  test("embedding with nesting") {
    val conf1 = emp ++ (a0 --> b1) ++ (b1 --> c1) ++ (b1 --> cc1)
    val morphs1 = (conf1 morphisms conf1).toSeq
    assert(morphs1.length == 2, morphs1.mkString("Morphs\n","\n  ",""))
    val conf2 = emp ++ (a0 --> b0) ++ (b0 --> c1) ++ (b0 --> cc1)
    val morphs2 = (conf2 morphisms conf2).toSeq
    assert(morphs2.length == 4, morphs2.mkString("Morphs\n","\n  ",""))
    val morphs3 = (conf2 morphisms conf1).toSeq
    assert(morphs3.length == 0, morphs3.mkString("Morphs\n","\n  ",""))
    val morphs4 = (conf1 morphisms conf2).toSeq
    assert(morphs4.length == 0, morphs4.mkString("Morphs\n","\n  ",""))
  }

  test("undfolding") {
    def checkUnfold( c1: DepthBoundedConf[LocDBCT],
                     c2: DepthBoundedConf[LocDBCT],
                     c2_unfold: DepthBoundedConf[LocDBCT],
                     m: Map[Thread[Loc],Thread[Loc]] ) = {
      assert(c1 <= c2_unfold)
      assert(c2 <= c2_unfold)
      assert(!c2_unfold.morphism(c2).isEmpty)
      assert(m.keys.forall(x => m.keys.forall(y => {
        if (c1(x)(y)) c2_unfold(m(x))(m(y))
        else true
      })))
    }
    
    val conf1 = emp ++ (a0 --> b0)
    val conf2 = emp ++ (a0 --> b1)
    val m12 = conf1.morphism(conf2).get
    val (conf21, _m12) = conf2.unfold(conf1, m12)
    
    checkUnfold(conf1, conf2, conf21, _m12)

    val conf3 = conf2 ++ (b1 --> c2)
    val m13 = conf1.morphism(conf3).get
    val (conf31, _m13) = conf3.unfold(conf1, m13)
    
    checkUnfold(conf1, conf3, conf31, _m13)

    val a01 = Thread[Loc](A,0)
    val conf4 = conf3 ++ (a01 --> c1)
    val m14 = conf1.morphism(conf3).get
    val (conf41, _m14) = conf4.unfold(conf1, m14)
    
    val conf5 = conf4 ++ (b1 --> a0)
    val m15 = conf1.morphism(conf5).get
    val (conf51, _m15) = conf5.unfold(conf1, m15)

    checkUnfold(conf1, conf5, conf51, _m15)

    val manyUnfold = emp ++ (a0 --> b0) ++ (b0 --> c0) ++ (b0 --> cc0)
    val m23 = manyUnfold.morphism(conf3).get
    val (conf32, _m23) = conf3.unfold(manyUnfold, m23)
    checkUnfold(manyUnfold, conf3, conf32, _m23)

  }

  test("folding") {
    val conf0 = emp ++ (mkB --> a0) ++ ((mkB++) --> a0)
    val fold0 = conf0.fold
    val gold0 = emp ++ ((mkB++) --> a0)
    assert(fold0 isSubgraphOf gold0)
    assert(gold0 isSubgraphOf fold0)

    val conf1 = emp ++ (b1 --> a0) ++ ((mkC++) --> b1) ++ ((mkC++) --> b1)
    val fold1 = conf1.fold
    val gold1 = conf1

    assert(fold1 isSubgraphOf gold1)
    assert(gold1 isSubgraphOf fold1)

    val conf2 = emp ++ (b0 --> a0) ++ (b1 --> a0) ++ (c1 --> b1) ++ (mkC --> b0) ++ (mkC --> b0)
    val fold2 = conf2.fold
    val gold2 = conf2
    assert(fold2 isSubgraphOf gold2)
    assert(gold2 isSubgraphOf fold2)

    val b12 = b0++
    val conf3 = emp ++ (b12 --> a0) ++ (b1 --> a0) ++ (c2 --> b12) ++ ((mkC++) --> b1) ++ ((mkC++) --> b1)
    val fold3 = conf3.fold
    val gold3 = emp ++ (b1 --> a0) ++ (c2 --> b1)
          
    assert(fold3 isSubgraphOf gold3)
    assert(gold3 isSubgraphOf fold3)
  }

  test("flattening 000") {
    val conf0 = emp + a0 + b1 + c2
    val (flat0, _) = conf0.flatten
    val expected0 = emp + a0 + b1 + c1
    println("conf0:" + conf0)
    println("flat0:" + flat0)

    val conf1 = emp ++ (a0 --> b1) ++ (b1 --> c2) ++ (a0 --> cc2)
    val (flat1, _) = conf1.flatten
    val expected1 = emp ++ (a0 --> b1) ++ (a0 --> cc1) ++ (b1 --> c2)
    assert(flat1 isSubgraphOf expected1)
    assert(expected1 isSubgraphOf flat1)
    
    val conf2 = emp ++ (a2 --> b2) ++ (b2 --> c2)
    val (flat2, _) = conf2.flatten
    val expected2 = emp ++ (a1 --> b1) ++ (b1 --> c1)
    assert(flat2 isSubgraphOf expected2)
    assert(expected2 isSubgraphOf flat2)

  }
  
  private val testDir = "core/src/test/resources/dbp_graph/graphs/"
  private def getFileContent(fName: String): String = {
    val fn = testDir + fName
    IO.readTextFile(fn)
  }

  test("flattening 001") {
    val graph = picasso.frontend.dbpGraph.DBPGraphParser.parseGraph(getFileContent("flatten_test_1.graph")).get
    val (flat, map) = graph.flatten
    //println("graph :\n" + graph)
    //println("flat :\n" + flat)
    //println("map:\n" + map.mkString("  ", "\n  ", ""))
    assert(map.exists{case (a,b) => a != b})
    //TODO the result of this is what we expect, find out what generates the funny graph in the first place!
  }

  test("subgraph 01") {
    val conf0 = emp + a1 + c0
    val conf1 = emp ++ (a1 --> b0) ++ (c0 --> b0)
    val conf2 = emp ++ (a1 --> b1) ++ (c0 --> b1)
    val conf3 = emp ++ (a1 --> b2) ++ (c0 --> b2)
    
    assert(conf0 isSubgraphOf conf0)
    assert(conf0 isSubgraphOf conf1)
    assert(conf0 isSubgraphOf conf2)
    assert(conf0 isSubgraphOf conf3)

    assert(!(conf1 isSubgraphOf conf0))
    assert(conf1 isSubgraphOf conf1)
    assert(!(conf1 isSubgraphOf conf2))
    assert(!(conf1 isSubgraphOf conf3))

    assert(!(conf2 isSubgraphOf conf0))
    assert(!(conf2 isSubgraphOf conf1))
    assert(conf2 isSubgraphOf conf2)
    assert(conf2 isSubgraphOf conf3)

    assert(!(conf3 isSubgraphOf conf0))
    assert(!(conf3 isSubgraphOf conf1))
    assert(!(conf3 isSubgraphOf conf2))
    assert(conf3 isSubgraphOf conf3)
  }

  test("subgraph 02"){
    import picasso.frontend.dbpGraph._
    val small = DBPGraphParser.parseGraph(getFileContent("widen_error_1_part_1.graph")).get
    val big   = DBPGraphParser.parseGraph(getFileContent("widen_error_1_part_2.graph")).get
    //println("small:\n" + small.toGraphviz("DBC"))
    //println("big:\n" + big.toGraphviz("DBC"))
    val ms = small morphisms big
    assert(ms.isEmpty)
    assert(! (small isSubgraphOf big) )
  }


  test("subgraph 03"){
    import picasso.frontend.dbpGraph._
    val small = DBPGraphParser.parseGraph(getFileContent("widen_error_2_part_1.graph")).get
    val big   = DBPGraphParser.parseGraph(getFileContent("widen_error_2_part_2.graph")).get
    //println("small:\n" + small.toGraphviz("DBC"))
    //println("big:\n" + big.toGraphviz("DBC"))
    val ms = small morphisms big
    assert(ms.isEmpty)
    assert(! (small isSubgraphOf big) )
  }



}
