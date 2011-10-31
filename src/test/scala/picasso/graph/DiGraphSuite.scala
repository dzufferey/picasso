package picasso.graph

import org.scalatest._
import Ordering._

class DiGraphSuite extends FunSuite {

  implicit def N(x: Int) = Vertex[Int](x)

  class IGT extends GT {
    type V = Vertex[Int]
  }

  //auxiliary fct to generate graphs.
  def gridAnd(other: List[(Vertex[Int],Vertex[Int])]): List[(Vertex[Int],Vertex[Int])] = {
    other :::
    (for (i <- 0 until 100 if i % 10 != 9) yield (N(i), N(i+1)) ).toList :::
    (for (i <- 0 until 9; j <- 0 until 10) yield (N(i*10 + j), N((i+1)*10 + j)) ).toList
  }
  def kn(n: Int): List[(Vertex[Int],Vertex[Int])] = {
    (for (i <- 0 until n; j <- 0 until n) yield (N(i), N(j)) ).toList
  }
  def knn(n1: Int, n2: Int): List[(Vertex[Int],Vertex[Int])] = {
    (for (i <- 0 until n1; j <- n1 until n1+n2) yield (N(i), N(j)) ).toList :::
    (for (i <- 0 until n1; j <- n1 until n1+n2) yield (N(j), N(i)) ).toList
  }
  def linkedList(n1: Int, n2: Int): List[(Vertex[Int],Vertex[Int])] = {
    if (n1 <= n2) (for (i <- n1 until n2) yield (N(i), N(i+1)) ).toList
    else (for (i <- n2 until n1) yield (N(i+1), N(i)) ).toList
  }
  def doublyLinkedList(n1: Int, n2: Int): List[(Vertex[Int],Vertex[Int])] = {
    if (n1 <= n2) {
      (for (i <- n1 until n2) yield (N(i), N(i+1)) ).toList :::
      (for (i <- n1 until n2) yield (N(i+1), N(i)) ).toList
    } else {
      (for (i <- n2 until n1) yield (N(i), N(i+1)) ).toList :::
      (for (i <- n2 until n1) yield (N(i+1), N(i)) ).toList
    }
  }
     
  test("testing add, remove, ...") {
    //empty LabeledDiGraph where the labels are the parity of the node id.
    val d1 = LabeledDiGraph.empty[IGT{type VL = Boolean; type EL = Int}](_.value % 2 == 0)

    val d2 = d1 + 356

    assert(!(d1 contains 356))
    assert(d2 contains 356)

    val d3 = d2 ++ (N(12)-(0)->(23))
    assert(d3(12, 0)(23))
    assert(d3(12, 0).size == 1)
    assert(d3(23, 0).size == 0)

    assert(d3.vertices.size == 3)
    assert(d3.vertices(356))
    assert(d3.vertices(12))
    assert(d3.vertices(23))

    assert((d3 - 356) contains (12,0,23))
    val d4 = d3 - 23
    assert(! (d4 contains 23))
    assert(d4 contains 356)
    assert(d4 contains 12)
    assert(d4(12, 0).size == 0)
  }

  type LIGT = IGT{type VL = Int; type EL = Int}
  type NIGT = IGT{type VL = Int; type EL = Unit}
  type EIGT = IGT{type VL = Unit; type EL = Int}
  type UIGT = IGT{type VL = Unit; type EL = Unit}

  test("testing traces") {
    val edges1 = N(0)-0->1 :: N(1)-1->1 :: N(1)-0->2 :: N(2)-1->3 :: N(3)-0->3 :: Nil
    val edges2 = N(0)-0->1 :: N(1)-1->1 :: N(1)-0->0 :: N(0)-1->1 :: N(1)-0->1 :: Nil
    val d1 = (LabeledDiGraph.empty[LIGT](_.value) /: edges1) (_ ++ _)
    val d2 = (LabeledDiGraph.empty[LIGT](_.value % 2) /: edges2) (_ ++ _)
    
    val t1 = Trace[Vertex[Int],Int](0)
    val t2 = Trace[Vertex[Int],Int](1)
    val t3 = Trace[Vertex[Int],Int](2)
    val t4 = Trace[Vertex[Int],Int](3)
    val t5 = Trace[Vertex[Int],Int](4)
    assert( (d1 isTraceValid t1) &&  (d2 isTraceValid t1))
    assert( (d1 isTraceValid t2) &&  (d2 isTraceValid t2))
    assert( (d1 isTraceValid t3) && !(d2 isTraceValid t3))
    assert( (d1 isTraceValid t4) && !(d2 isTraceValid t4))
    assert(!(d1 isTraceValid t5) && !(d2 isTraceValid t5))

    val t11 = Trace[Vertex[Int],Int](0, 0 -> N(1) )
    val t12 = Trace[Vertex[Int],Int](0, 1 -> N(1) )
    val t13 = Trace[Vertex[Int],Int](1, 0 -> N(1) )
    val t14 = Trace[Vertex[Int],Int](1, 1 -> N(1) )
    val t15 = Trace[Vertex[Int],Int](0, 0 -> N(0) )
    val t16 = Trace[Vertex[Int],Int](3, 0 -> N(3) )
    assert( (d1 isTraceValid t11))
    assert(d2 isTraceValid t11)
    assert( (d1 isTraceValid t11) &&  (d2 isTraceValid t11))
    assert(!(d1 isTraceValid t12) &&  (d2 isTraceValid t12))
    assert(!(d1 isTraceValid t13) &&  (d2 isTraceValid t13))
    assert( (d1 isTraceValid t14) &&  (d2 isTraceValid t14))
    assert(!(d1 isTraceValid t15) && !(d2 isTraceValid t15))
    assert( (d1 isTraceValid t16) && !(d2 isTraceValid t16))

    val t21 = Trace[Vertex[Int],Int](0, 0 -> N(1), 0 -> N(2))
    val t22 = Trace[Vertex[Int],Int](0, 0 -> N(1), 0 -> N(0))
    val t23 = Trace[Vertex[Int],Int](0, 0 -> N(1), 1 -> N(1))
    val t24 = Trace[Vertex[Int],Int](1, 0 -> N(2), 1 -> N(3))
    val t25 = Trace[Vertex[Int],Int](1, 0 -> N(0), 1 -> N(1))
    assert( (d1 isTraceValid t21) && !(d2 isTraceValid t21))
    assert(!(d1 isTraceValid t22) &&  (d2 isTraceValid t22))
    assert( (d1 isTraceValid t23) &&  (d2 isTraceValid t23))
    assert( (d1 isTraceValid t24) && !(d2 isTraceValid t24))
    assert(!(d1 isTraceValid t25) &&  (d2 isTraceValid t25))

    //TODO longer traces
  }
  
  test("testing shortest path") {
    
    val empty0 = DiGraph.empty[UIGT]
    intercept[java.lang.RuntimeException] {
      empty0.shortestPath(1,1)
    }
    
    val empty1 = empty0 + 1
    intercept[java.lang.RuntimeException] {
      empty1.shortestPath(1,2)
    }
    intercept[java.lang.RuntimeException] {
      empty1.shortestPath(2,1)
    }

    val empty2 = empty1 + 2
    assert(empty2.shortestPath(1,1).length == 0)
    assert(empty2.shortestPath(2,2).length == 0)
    intercept[java.lang.RuntimeException] {
      empty2.shortestPath(1,2)
    }
    
    
    val grid0 = DiGraph[UIGT](gridAnd(Nil))
    assert(grid0.shortestPath(0,99).length == 18)
    assert(grid0 isTraceValid grid0.shortestPath(0,99))
    val grid1 = DiGraph[UIGT](gridAnd(List((0,99))))
    assert(grid1.shortestPath(0,99).length == 1)
    assert(grid1 isTraceValid grid0.shortestPath(0,99))
    assert(grid1 isTraceValid grid1.shortestPath(0,99))
    assert(! (grid0 isTraceValid grid1.shortestPath(0,99)))
    val grid2 = DiGraph[UIGT](gridAnd(List((0,9))))
    assert(grid2.shortestPath(0,99).length == 10)
    assert(grid2 isTraceValid grid2.shortestPath(0,99))
    val grid3 = DiGraph[UIGT](gridAnd(List((0,70))))
    assert(grid3.shortestPath(0,99).length == 12)
    assert(grid3 isTraceValid grid3.shortestPath(0,99))
    val grid4 = DiGraph[UIGT](gridAnd(List((0,70),(70,40),(40,0))))
    assert(grid4.shortestPath(0,99).length == 12)
    assert(grid4 isTraceValid grid4.shortestPath(0,99))
    assert(grid4 isTraceValid grid3.shortestPath(0,99))
    assert(grid3 isTraceValid grid4.shortestPath(0,99))

    //TODO more complex strucutres
  }

  implicit def D(x: Double) = Vertex[Double](x)

  class NDGT extends GT {
    type V = Vertex[Double]
    type VL = Int
    type EL = Unit
  }
  
  test("testing graph homomorphisms") {
    //TODO the subgraph relation should be
    // (1) reflexive,
    // (2) transitive, and
    // (3) anti-symmetric.
    
    val emptyLDG = LabeledDiGraph.empty[IGT{type VL=Unit; type EL=Int}](x => ())
    val emptyDG = DiGraph.empty[UIGT]
    assert(emptyDG.subgraphIsomorphism(emptyDG).get.isEmpty)
    
    assert(emptyLDG.subgraphIsomorphism(emptyLDG).get.isEmpty)
    //assert(emptyDG.subgraphIsomorphism(emptyLDG).get.isEmpty)
    //assert(emptyLDG.subgraphIsomorphism(emptyDG).get.isEmpty)
    
    val emptyLDG1 = emptyLDG + 1
    val emptyDG1 = emptyDG + 1

    assert(emptyDG1.subgraphIsomorphism(emptyDG1).get.apply(1) == N(1))
    assert(emptyLDG1.subgraphIsomorphism(emptyLDG1).get.apply(1) == N(1))
    //assert(emptyLDG1.subgraphIsomorphism(emptyDG1).get.apply(1) == 1)
    
    assert(emptyDG1.subgraphIsomorphism(emptyDG).isEmpty)
    assert(emptyDG.subgraphIsomorphism(emptyDG1).get.isEmpty)
    assert(emptyLDG.subgraphIsomorphism(emptyLDG1).get.isEmpty)

    val dg0 = emptyDG ++ (N(1)-->1)
    val dg1 = emptyDG ++ (N(1)-->2)
    //assert(emptyDG1.subgraphIsomorphism(dg0).get.apply(1) == 1)
    //assert(emptyDG1.subgraphIsomorphism(dg1).get.apply(1) == 1)
    assert(dg0.subgraphIsomorphism(dg0).get.apply(1) == N(1))
    assert(dg1.subgraphIsomorphism(dg1).get.apply(1) == N(1))
    assert(dg1.subgraphIsomorphism(dg1).get.apply(2) == N(2))
    assert(dg1.subgraphIsomorphism(dg0).isEmpty)
    assert(dg0.subgraphIsomorphism(dg1).isEmpty)

    //labels on the nodes
    val nigtEmp = NodeLabeledDiGraph.empty[NIGT](x => x.value)
    val ndgtEmp = NodeLabeledDiGraph.empty[NDGT]((x: Vertex[Double]) => x.value.toInt)
    val ks0 = nigtEmp ++ (N(1)-->2) ++ (N(2)-->3) 
    val ks1 = ndgtEmp ++ (D(1.1)-->2.9) ++ (D(2.9)-->3.3)
    val ks2 = ndgtEmp ++ (D(1.1)-->2.9) ++ (D(2.8)-->3.3)
    val ks3 = ndgtEmp ++ (D(0.1)-->2.9) ++ (D(2.9)-->3.3)
    val ks4 = NodeLabeledDiGraph.empty[NIGT]((x: Vertex[Int]) => x.value % 2) ++ (N(1)-->2) ++ (N(2)-->3)
    assert(ks0.subgraphIsomorphism(ks0).isDefined)
    assert(ks1.subgraphIsomorphism(ks1).isDefined)
    assert(ks2.subgraphIsomorphism(ks2).isDefined)
    assert(ks3.subgraphIsomorphism(ks3).isDefined)
    assert(ks0.subgraphIsomorphism(ks1).isDefined)
    assert(ks1.subgraphIsomorphism(ks0).isDefined)
    assert(ks0.subgraphIsomorphism(ks2).isEmpty)
    assert(ks0.subgraphIsomorphism(ks3).isEmpty)
    assert(ks0.subgraphIsomorphism(ks4).isEmpty)
    //assert(ks4.subgraphIsomorphism(ks0).isEmpty)

    //labels on the edges
    val eigtEmp = EdgeLabeledDiGraph.empty[EIGT]
    val ldg0 = eigtEmp ++ (N(1)-0->1)
    val ldg1 = eigtEmp ++ (N(1)-2->1)
    assert(ldg0.subgraphIsomorphism(ldg0).get.apply(1) == N(1))
    assert(ldg1.subgraphIsomorphism(ldg1).get.apply(1) == N(1))
    assert(ldg0.subgraphIsomorphism(ldg1).isEmpty)
    assert(ldg1.subgraphIsomorphism(ldg0).isEmpty)

    //non-injective morphisms
    val dg10 = DiGraph.empty[UIGT] ++ (N(2)-->3) ++ (N(2)-->4)
    val dg11 = DiGraph.empty[UIGT] ++ (N(1)-->2)
    val hom = dg10.morphism[UIGT](dg11, {x => x.value == 1}, ((_,_) => true))
    assert(!hom.isEmpty)
    assert(hom.get.apply(2) == N(1))
    assert(hom.get.apply(3) == N(2))
    assert(hom.get.apply(4) == N(2))

    //TODO more: linked list, doubly linked list, grid, K_n, K_nn, ...
    //pending
  }

  test("reverse (checks it is not losing nodes anymore)") {
    val chain = DiGraph[UIGT](linkedList(0,10))
    assert(chain.vertices.size == 11)
    assert(chain.reverse.vertices.size == 11)
  }

  def checkTopSort[G <: GT.ULGT](graph: DiGraph[G], topSort: Seq[G#V]): Boolean = {
    graph.vertices forall (v => {
      val pred = topSort.takeWhile(_ != v)
      val succ = graph(v)
      !(pred exists (succ(_)))
    })
  }

  test("Topological sort of graph"){
    val chain = DiGraph[UIGT](linkedList(0,10))
    val topsortChain = chain.topologicalSort
    checkTopSort[UIGT](chain, topsortChain)
  }


  test("transitive closure"){
    val chain = DiGraph[UIGT](linkedList(0,10)).transitiveClosure
    for (i <- 0 to 10; j <- i+1 to 10) assert(chain(i)(j))
  }
  
  test("reflexive transitive closure"){
    val chain = DiGraph[UIGT](linkedList(0,10)).reflexiveTransitiveClosure
    for (i <- 0 to 10; j <- i to 10) assert(chain(i)(j))
  }

  test("AI fixpoint"){
    val incr = 1
    val decr = -1
    val reset = 0
    val greaterThan5 = 5
    val lower = -10
    val upper = 10
    import scala.math._
    
    def bound(p: (Int,Int)) = (max(lower, min(upper, p._1)),max(lower, min(upper, p._2)))
    def post(d: Option[(Int,Int)], op: Int) = op match {
      case `incr` => d map (p => (p._1 + 1, p._2 + 1)) map bound
      case `decr` => d map (p => (p._1 - 1, p._2 - 1)) map bound
      case `reset` => Some((0, 0))
      case `greaterThan5` => d flatMap (p => if (p._2 > 5) Some(max(6, p._1), p._2) else None) 
      case _ => sys.error("not a valid operation")
    }
    def join(d1: Option[(Int,Int)], d2: Option[(Int,Int)]) =
      d1 map (p1 => d2 map (p2 => (min(p1._1, p2._1), max(p1._2, p2._2))) getOrElse p1) orElse d2
    def cover(d1: Option[(Int,Int)], d2: Option[(Int,Int)]) =
      d1 map (p1 => d2 map (p2 => p1._1 <= p2._1 && p1._2 >= p2._2) getOrElse true) getOrElse (d2.isEmpty)

    val edges = (N(0),reset,N(1)) :: (N(1),incr,N(1)) :: (N(1),decr,N(1)) :: (N(1),greaterThan5,N(2)) :: Nil
    val graph = EdgeLabeledDiGraph.empty[EIGT] ++ edges
    val ai = graph.aiFixpoint(post, join, cover, (_ => None))
    //Console.println(graph)
    //Console.println(ai(0))
    //Console.println(ai(1))
    //Console.println(ai(2))
    assert(ai(0) == None);
    assert(ai(1) == Some((lower, upper)));
    assert(ai(2) == Some(6, upper));
  }
    
  test("simplePaths"){
    //labels on the edges
    val empty = EdgeLabeledDiGraph.empty[EIGT]
    val graph = empty ++ (N(0)-0->1) ++ (N(1)-1->1) ++ (N(1)-2->3) ++ (N(3)-2->1) ++ (N(1)-4->4)
    val pathes = graph.simplePaths
    assert(pathes.length == 4)
    val expected = List(Trace[Vertex[Int],Int](0, 0 -> N(1)),
                        Trace[Vertex[Int],Int](1, 1 -> N(1)),
                        Trace[Vertex[Int],Int](1, 2 -> N(3), 2 -> N(1)),
                        Trace[Vertex[Int],Int](1, 4 -> N(4))
                       )
    expected foreach ( p => assert(pathes contains p, "not contains: " + p ))
  }

  test("trace Split"){
    val t1 = Trace[Vertex[Int],Int](0, 0 -> N(1))
    assert(t1.split(0).length == 1)
    assert(t1.split(1).length == 1)
    assert(t1.split(2).length == 1)
    val t2 = Trace[Vertex[Int],Int](1, 1 -> N(1))
    assert(t2.split(0).length == 1)
    assert(t2.split(1).length == 1)
    assert(t2.split(2).length == 1)
    val t3 = Trace[Vertex[Int],Int](1, 2 -> N(2), 2 -> N(1))
    assert(t3.split(0).length == 1)
    assert(t3.split(1).length == 1)
    assert(t3.split(2).length == 2)
  }

}

