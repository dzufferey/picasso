package picasso.model

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.math._
import picasso.math.WellPartialOrdering._
import picasso.graph._


class Thread[State](val state: State, val depth: Int) 
extends VertexLike[Thread[State]] {
  override def toString = super.toString + "-" + label.toString
  override def clone = Thread[State](state, depth)
  def ++ = Thread[State](state, depth + 1)
  def -- = Thread[State](state, depth - 1)
  def label = (state, depth)
}

object Thread {
  def apply[State](state: State, depth: Int = 0) : Thread[State] = {
    new Thread(state, depth)
  }
}

trait DBCT extends GT {
  type State
  type V = Thread[State]
  type VL = (State, Int)
}

class DepthBoundedConf[P <: DBCT](edges: Map[P#V, Map[P#EL, Set[P#V]]], label: P#V => P#VL)
extends GraphLike[DBCT,P,DepthBoundedConf](edges, label) {

  override def toString = toGraphviz("DBC")

  override type Self = DepthBoundedConf[P] 
  override def companion = DepthBoundedConf
  override def labelOf(x: V) = x label

  type Morphism = Map[V, V]
  type Edges = Map[V, Map[EL, Set[V]]]
  type UndirectedAdjacencyMap = Map[V, Set[V]]

  // use def instead of val if caching requires too much space
  val undirectedAdjacencyMap = {
    val out = adjacencyMap mapValues (_.foldLeft(Set.empty[V])((xs, e) => e._2 ++ xs))
    out.foldLeft(out)((acc, p) => p._2.foldLeft(acc)((acc, x) => acc + ((x, acc.getOrElse(x, Set.empty[V]) + p._1))))
  }

  protected def propagate(ms: MorphState[P], i : Int, j : Int) = {
    val (tableSmaller, tableBigger, nodesSmaller, nodesBigger, compatible) = ms
    val v = nodesSmaller(i)
    val vSucc = undirectedAdjacencyMap(v)
    val w = nodesBigger(j)

    for (k <- i+1 until nodesSmaller.size; if (compatible(k) contains j)) {
      val u = nodesSmaller(k)
      val uSucc = undirectedAdjacencyMap(u)
      val common = vSucc & uSucc
      if (common.exists(n => compatible(tableSmaller(n)).forall(l => nodesBigger(l).depth >= w.depth)))
        compatible.update(k, compatible(k) - j)
    }

    
    //Logger("TEST", LogNotice, "common: " + common)
    //Logger("TEST", LogNotice, "v: " + v)
    //Logger("TEST", LogNotice, "u: " + u)
    //Logger("TEST", LogNotice, "mergeable: " + merge)
  }

  def morphisms(bigger: Self, partialMorph: Morphism = Map.empty[V,V])(implicit wpo: WellPartialOrdering[P#State]) : Iterator[Morphism] = 
    lazyMorphisms[P](bigger, _.depth == 0, ((ms,i,j) => propagate(ms,i,j)), partialMorph)

  def morphism(bigger: Self)(implicit wpo: WellPartialOrdering[P#State]) : Option[Morphism] = 
    morphism[P](bigger, _.depth == 0, ((ms,i,j) => propagate(ms,i,j)))
  
  def degree(v: V): Int = undirectedAdjacencyMap(v).size

  override protected def mkLookup: (Map[V,Int], IndexedSeq[V]) = {
    val sortFun = { (v: V, w: V) => v.label._2 > w.label._2 || (v.label._2 == w.label._2 && degree(v) > degree(w)) }
    val vs: IndexedSeq[V] = vertices.toIndexedSeq.sortWith(sortFun)
    val table: Map[V,Int] = (Map.empty[V,Int] /: vs.indices)( (table, i) => table + (vs(i) -> i))
    (table, vs)
  }

  def unfold(smaller: Self, m: Morphism): (Self, Morphism) = {
    
    val smallerAdj = smaller.undirectedAdjacencyMap

    val biggerAdj = this.undirectedAdjacencyMap

    def unfold(m: Morphism, biggerAdj: UndirectedAdjacencyMap, bigger: Edges): (Morphism, Edges) = {
      def copyComponent(new_m: Morphism, todo : List[(Option[V], V)], cloneMap: Map[V, V]) : (Morphism, UndirectedAdjacencyMap, Edges) = {
        val totalCloneMap = (x: V) => cloneMap.getOrElse(x,x)
        todo match {
          case Nil => {
            // Duplicate edges for cloned nodes
            val new_bigger: Edges = {
              val old_new_edges: Edges =
                bigger.map[(V,Map[EL, Set[V]]),Edges](p => {
                  val y = p._1
                  val es = p._2
                  if (!(cloneMap isDefinedAt y)) (y, es mapValues (ys => ys ++ (ys collect cloneMap)))
                  else (y, es)})
              val cloned_new_edges: Edges = 
                bigger.collect[(V,Map[EL, Set[V]]),Edges] 
                  {case (y, es) if cloneMap isDefinedAt y => (cloneMap(y), es mapValues (ys => ys map totalCloneMap))}
              old_new_edges ++ cloned_new_edges
            }
            val new_biggerAdj: UndirectedAdjacencyMap = 
              (biggerAdj.map[(V,Set[V]),UndirectedAdjacencyMap] (p => {
                val y = p._1
                val y1s = p._2
                if (!(cloneMap isDefinedAt y)) (y, y1s ++ (y1s collect cloneMap))
                else (y, y1s)})) ++
              biggerAdj.collect[(V,Set[V]),UndirectedAdjacencyMap] {case (y, y1s) if cloneMap isDefinedAt y => (cloneMap(y), y1s map totalCloneMap)}
            (new_m, new_biggerAdj, new_bigger)
          }
          case (opt_x, y) :: todo1 => {
            if ((cloneMap contains y) || y.depth == 0) {
              val new_m1 = 
                opt_x match {
                  case None => new_m
                  case Some(x) => new_m + ((x, totalCloneMap(y)))
                }
              copyComponent(new_m1, todo1, cloneMap) 
            } else {
              val y_clone = y--
              val new_cloneMap = cloneMap + ((y, y_clone))
              val new_m1 = 
                opt_x match {
                  case None => new_m
                  case Some(x) => new_m + ((x, y_clone))
                }
              val todo_left =
                opt_x match {
                  case None => Nil
                  case Some(x) =>
                    (smallerAdj(x) map (x1 => (Some(x1), m(x1)))) toList
                }
              val todo_right = (biggerAdj(y) map ((None, _))) toList
              val new_todo = todo_left ++ todo1 ++ todo_right
              copyComponent(new_m1, new_todo, new_cloneMap)
            }
          }
        }
      }

      // pick seed node in some replication component
      val seed = m find (_._2.depth > 0)
      
      seed match {
        case None => (m, bigger)
        case Some(p) => {
          val new_acc = copyComponent(m, List((Some(p._1), p._2)), Map.empty[V,V])
          unfold(new_acc._1, new_acc._2, new_acc._3)
        }
      }
    }

    val res = unfold(m, biggerAdj, edges)
    (DepthBoundedConf[P](res._2), res._1)
  }

  def fold(implicit wpo: WellPartialOrdering[P#State]): Self = {
    val iter = this morphisms this

    def loop() : Self = {
      if (iter.hasNext) { 
        val m = iter.next

        val used: Set[V] = (Set.empty[V] /: m)((acc, p) => acc + p._2)
        val redundant = vertices &~ used
        
        if (redundant.isEmpty) loop()
        else this -- redundant
      } else this
    }

    loop()    
  }

  def widen(newThreads: Set[V]): Self = {

    def processSeed(depth: Int, newThreads: Set[V], threadsInc: Map[V, V]): Map[V, V] = {
      newThreads find (v => (v.depth == depth) && (depth == 0 || (undirectedAdjacencyMap(v) exists (w => (w.depth == depth) && !(newThreads contains w))))) match {
        case Some(seed) =>
          def processComponent(todo: Set[V], newThreads: Set[V], threadsInc: Map[V, V]): Map[V, V] = {
            todo headOption match {
              case Some(v) => {
                val vInc = v++
                val newTodo = todo ++ (undirectedAdjacencyMap(v) filter (newThreads contains)) - v
                processComponent(newTodo, newThreads - v, threadsInc + (v -> vInc))
              }
              case None =>
                processSeed(depth, newThreads, threadsInc)
            }
          }
          processComponent(Set(seed), newThreads, threadsInc)
        case None => 
          val newThreads1 = newThreads filter (_.depth > depth)
          if (!newThreads1.isEmpty) 
            processSeed(depth + 1, newThreads1, threadsInc)
          else threadsInc
      }
    }

    val mapping = processSeed(0, newThreads, Map.empty[V,V])
    this morph mapping
  }

  override def clone: (Self, Morphism) = {
    val m = (Map.empty[V,V] /: vertices){ (acc, v) => acc + (v -> v.clone)}
    (this morph m, m)
  }

}


object DepthBoundedConf extends GraphFactory[DBCT, DepthBoundedConf]{
  override def apply[P <: DBCT](edges: Map[P#V, Map[P#EL, Set[P#V]]], label: P#V => P#VL) = new DepthBoundedConf[P](edges, label)
  def apply[P <: DBCT](edges: Map[P#V, Map[P#EL, Set[P#V]]]): DepthBoundedConf[P] = {
    val label = {(v: P#V) => v label}
    apply[P](edges, label)
  }
  
  def empty[P <: DBCT]: DepthBoundedConf[P] = {
    val label = {(v: P#V) => v label}
    empty[P](label)
  }


  implicit def wellPartiallyOrdered[P <: DBCT](c: DepthBoundedConf[P])(implicit ev: WellPartialOrdering[P#State]) =
    new WellPartiallyOrdered[DepthBoundedConf[P]] {
      def tryCompareTo (that: DepthBoundedConf[P]): Option[Int] = {
        //print("tryCompareTo: ")
        //print("c = " + c)
        //print("that = " + that)
        if (c eq that) Some(0) else
          c morphism that match {
            case Some(_) => 
              that morphism c match {
                case Some(_) => Some(0)
                case None => Some(-1)
              }
            case None => 
              that morphism c match {
                case Some(_) => Some(1)
                case None => None
              }
          } 
      }
    } 
}


class DepthBoundedTransition[P <: DBCT](id: String,
                                        lhs: DepthBoundedConf[P],
                                        rhs: DepthBoundedConf[P],
                                        hr: Map[P#V, P#V],
                                        hk: Map[P#V, P#V],
                                        inh: Option[DepthBoundedConf[P]] = None)(implicit wpo: WellPartialOrdering[P#State])
extends Transition[DepthBoundedConf[P]] 
{

  type Conf = DepthBoundedConf[P]
  type Morphism = Map[P#V, P#V]

  def apply(conf: Conf): Set[Conf] = {
    val homs = lhs.morphisms(conf)
    
    def removeInhibitors(conf: Conf, g: Morphism): Conf = {
      inh match {
        case Some(inhibitor) => {
          val gRestricted = g filter (p => inhibitor.vertices(p._1))
          val matches = inhibitor.morphisms(conf, gRestricted) 
          
          (conf /: matches) {
            (conf, m) =>
              val inhibited = m flatMap {p => if(g isDefinedAt p._1) Set[P#V]() else Set[P#V](p._2)}
              val coercedConf = conf -- inhibited 
              coercedConf
          }
        }
        case None => conf
      }
    }

    def post(g: Morphism): Conf = {
      val (conf0, g1) = conf.unfold(lhs, g)
      //print("conf1: " + conf1)
      //print("lhs: " + lhs.morph(g1))

      // remove all inhibiting subgraphs from conf0 (monotonicity abstraction)
      val conf1 = removeInhibitors(conf0, g1)
      
      // Compute nodes that the transition removes from conf1
      val hkRange = hk.values
      val removed = lhs.vertices.flatMap{v => if((hr isDefinedAt v) || (hkRange exists (_ == v))) Set[P#V]() else Set[P#V](g1(v))}
      //println ("removed: " + removed)

      // Frame is conf1 w/o the matched lhs and w/o dangling edges to removed nodes
      val frame = conf1 -- (lhs.morph(g1)) -- removed
      //print("frame: " + frame)      

      val (rhsClone, f) = rhs.clone

      // compute partial morphism conf1 -> rhs 
      val f_hr = hr.map[(P#V,P#V),Morphism]{p => (p._1, f(p._2))}
      val f_hr_g1 = g1.map[(P#V,P#V),Morphism]{p => (p._2, f_hr.getOrElse(p._1,p._2))}

      // compute partial morphism rhs -> conf1
      val hk_f = f.map[(P#V,P#V),Morphism]{p => (p._2, hk.getOrElse(p._1, p._2))}
      val g1_hk_f = hk_f mapValues (v => g1.getOrElse(v, v))
      //print("rhs: " + rhsClone)

      // add rhs to the frame and fold the result
      val postUnfolded = (frame morph f_hr_g1) ++ (rhsClone morph g1_hk_f)
      val post = postUnfolded.fold
      //print("post: " + post)
      post
    }

    homs.map(post).toSet
  }

  def isDefinedAt(conf: Conf): Boolean = true

  def toGraphviz(name: String, prefix: String = "digraph"): scala.text.Document = {
    import scala.text.Document._
    val inhib = inh.map(_.toGraphvizFull("cluster_"+name+"guard", "subgraph", "label = "+ Misc.quote("GUARD")+";", name+"guard")._1)
    val (pre, m1) = lhs.toGraphvizFull("cluster_"+name+"lhs", "subgraph", "label = "+ Misc.quote("LHS")+";", name+"lhs")
    val (post, m2) = rhs.toGraphvizFull("cluster_"+name+"rhs", "subgraph", "label = "+ Misc.quote("RHS")+";", name+"rhs")
    val title = if (prefix == "subgraph") empty :/: text("label = "+ Misc.quote(id)+";") else empty
    val name2 = if (prefix == "subgraph") "cluster_"+name else name
    val hrDoc = hr.filter{case (a,b) => (m1 contains a) && (m2 contains b)}.toList.map{case (a,b) => text( m1(a) + " -> " + m2(b) + "[color=\"#0000aa\"];")}
    val hkDoc = hk.filter{case (a,b) => (m2 contains a) && (m1 contains b)}.toList.map{case (a,b) => text( m1(b) + " -> " + m2(a) + "[dir=back color=\"#00aa00\"];")}
    //inh
    val mapEdges = hrDoc ::: hkDoc
    val body = ((title :/: (inhib getOrElse empty):/: pre :/: post) /: mapEdges)(_ :/: _)
    prefix :: " " :: name2 :: " {" :: nest(4, body) :/: text("}")
  }
}

object DepthBoundedTransition {
  def apply[P <: DBCT]( id: String,
                        lhs: DepthBoundedConf[P],
                        rhs: DepthBoundedConf[P],
                        h: Map[P#V, P#V],
                        hk: Map[P#V, P#V] = Map.empty[P#V, P#V],
                        inh: Option[DepthBoundedConf[P]] = None )(implicit wpo: WellPartialOrdering[P#State]): DepthBoundedTransition[P] = {
    new DepthBoundedTransition[P](id, lhs, rhs, h, hk, inh)(wpo)
  }
}



class DepthBoundedProcess[P <: DBCT](trs: List[DepthBoundedTransition[P]])(implicit wpoConf: WellPartialOrdering[DepthBoundedConf[P]], wpoState: WellPartialOrdering[P#State]) extends WSTS with WADL {
  type S = DepthBoundedConf[P]
  implicit val ordering : WellPartialOrdering[S] = wpoConf
  val stateOrdering = wpoState

  /** copy constructor */
  def this(dbp: DepthBoundedProcess[P]) = this(dbp.transitions)(dbp.ordering, dbp.stateOrdering)

  def toGraphviz(name: String): scala.text.Document = {
    import scala.text.Document._
    var x = 0
    val docOfTrs = trs map ( t => {
      x = x + 1
      t.toGraphviz("transition_"+x, "subgraph")
    })
    val oneDoc = docOfTrs.reduceRight(_ :/: _)
    "digraph" :: " " :: name :: " {" :: nest(4, empty :/: oneDoc) :/: text("}")
  }
  
  type T = DepthBoundedTransition[P]
  def transitions = trs

  def tryAcceleratePair(smaller: S, bigger: S): Option[S] = {
    smaller morphism bigger match {
      case None => None
      case Some(m) => {
        val newThreads = bigger.vertices -- m.values
        
        val accBigger = bigger widen newThreads

        //println("Acceleration:")
        //print(smaller.toGraphviz("smaller"))
        //print(bigger.toGraphviz("bigger"))
        //print(accBigger.toGraphviz("accBigger"))
        
        Some((bigger widen newThreads).fold)

        /*
        val threadsInc = new scala.collection.mutable.HashMap[S#V,S#V]
        val mapping: PartialFunction[S#V,S#V] = 
          threadsInc orElse { case v =>
            if (!(newThreads contains v)) v else {
              val vInc = v++
              threadsInc += (v -> vInc)
              vInc
            }
          }

        val accBigger = bigger morph mapping

        if (threadsInc.values.forall (_.depth > 1)) Some(bigger) else Some(accBigger)
        */
      }
    }
  }
}


/*
object PiProgram {
    
  def isConfiguration(p: PiProcess): Boolean  = p match {
    case Composition(processes) => processes.forall(isConfiguration)
    case Restriction(_, process) => isConfiguration(process)
    case Repetition(process) => isConfiguration(process)
    case PiZero => true
    case PiProcessID(_,_) => true
    case _ => false
  }
  
  import scala.collection.immutable.TreeMap
  def instanciateDefinition(pid: String, args: List[String], definition: Map[String,(List[String], PiProcess)]): PiProcess = definition get pid match {
    case Some((params, p)) => {
      val map = (TreeMap.empty[String,String] /: (params zip args))(_ + _)
      p alpha map
    }
    case None => error("PiProgram.instanciateDefinition: " + pid +" not found")
  }

  //TODO define normal form where equations have a prefix/choice/replication first
  //TODO normal form for the configuration: restriction at top level, or just below replication, then composition of PIDs

  private def removeRestrictions(configuration: PiProcess): PiProcess = configuration match {
    case Restriction(_, process) => removeRestrictions(process)
    case process => process
  }

  def findProcessID(configuration: PiProcess, id: String): List[PiProcessID] = {
    val stripped = removeRestrictions(configuration)
    configuration match {
      case Composition(processes) => {
        ((Nil: List[PiProcessID]) /: processes)( (acc, p) => p match {
          case pid @ PiProcessID(_,_) => pid::acc
          case Restriction(_,_) =>
            Logger("DepthBoundedProcess", LogWarning, "PiProgram.findProcessID does not yet handle restriction")
            acc
          case _ => error("PiProgram.findProcessID: configuration not in normal form (ProcessID/Restriction)")
        })
      }
      case _ => error("PiProgram.findProcessID: configuration not in normal form Composition")
    }
  }
    
}

object PiProcessWPO extends WellPartialOrdering[PiProcess] {

  def tryCompare(p1: PiProcess, p2: PiProcess): Option[Int] = {
    //TODO transform progams into some kind of graph and call somegraph isomosphism
    //put graph as lazy val into the process ?
    error("TODO")
  }

  def lteq(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(0) | Some(-1) => true; case _ => false }
  
  override def lt(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(-1) => true; case _ => false }
  
  override def equiv(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(0) => true; case _ => false }
  
  override def gteq(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(0) | Some(1) => true; case _ => false }
  
  override def gt(p1: PiProcess, p2: PiProcess): Boolean =
    tryCompare(p1, p2) match { case Some(1) => true; case _ => false }

}

/** a transition happening on (co-)name observable*/
class PiTransition(observable: String, definition: Map[String,(List[String], PiProcess)]) extends Transition[PiProcess] {

  private def findMatchingParams(p: PiProcess, template: (String,(List[String], PiProcess))): List[(String, List[String], PiProcess)] = {
    val matchingPID = PiProgram.findProcessID(p, template._1)
    matchingPID map { case PiProcessID(id, args) => 
      val zipped = template._2._1 zip args
      val substitution = (Map.empty[String,String] /: zipped)(_ + _)
      (id, args, template._2._2 alpha substitution)
    }
  }

  private def matchAndFilter(s: PiProcess, defs: Map[String,(List[String], PiProcess)]): List[(String,List[String], PiProcess)] = {
    defs.toList flatMap ( mapping => {
      val instanciated = findMatchingParams(s, mapping)
      instanciated filter (_._3 isObservablePrefix observable)
    })
  }


  private val receiving: Map[String,(List[String], PiProcess)] = definition filter ( (p: (String,(List[String], PiProcess))) => isInputPrefix(p._2._2))
  /** Returns the process ID that are receiving on observable */
  def name(s: PiProcess) = matchAndFilter(s, receiving)
  
  private val sending: Map[String,(List[String], PiProcess)] = definition filter ( (p: (String,(List[String], PiProcess))) => isOutputPrefix(p._2._2))
  /** Returns the process ID that are sending on observable */
  def coname(s: PiProcess) = matchAndFilter(s, sending)

  def apply(state: PiProcess): Set[PiProcess] = {
    error("TODO")
  }

  def isDefinedAt(state: PiProcess): Boolean = !(name(state).isEmpty || coname(state).isEmpty)
}
*/
//TODO extends WSTS with WADL
//class PiProgram(definition: Map[String,(List[String], PiProcess)], configuration: PiProcess) extends WSTS with PredBasis {
//
//  type S = PiProcess
//  implicit val ordering: WellPartialOrdering[S] = PiSubGraph
//  tpye T = ...
//  val transitions = Nil //TODO to have an easily computable #of transitions: a transition is givent by a pair of InputPrefix/OutputPrefix
//  def predBasis(s: UpwardClosedSet[S]): UpwardClosedSet[S] = error("TODO")
//  //TODO
//
//}
