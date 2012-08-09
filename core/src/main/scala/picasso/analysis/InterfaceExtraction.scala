package picasso.analysis

import picasso.utils._
import picasso.model.dbp._
import picasso.graph._
import picasso.math._
import TransitionsGraphFromCover._

object InterfaceExtraction {

  type ObjType = String
  type Field = String
  type UnaryPredicates = Map[String, Boolean]
  type BinaryPredicates = Map[String, Map[Field,Boolean]]
  //obj: class name, neighborhood (to what it is connected), unary predicates, binary predicates
  type Obj = (ObjType, Map[Field, Iterable[ObjType]], UnaryPredicates, BinaryPredicates)

  //types for the transitions and the language
  
  //modifiers for tracking the eq classes
  sealed abstract class Multiplicity
  case object One extends Multiplicity
  case object May extends Multiplicity
  case object Part extends Multiplicity
  case object Rest extends Multiplicity //Rest means All but ...

  type Changes[A] = Map[A, Iterable[(Multiplicity, A)]]

  // a graph type for the stripped configs
  class EqClass(val obj: Obj) {
    override def toString = objToString(obj)
  }

  type IGT = GT{type V = EqClass; type VL = String; type EL = String}
  type G = LabeledDiGraph[IGT]

  /** What happens each time a method is called.
   *  Src: the input
   *  Obj: the caller
   *  String: the method name
   *  Become: what an object becomes / might become
   *  Iterable[Obj]: the newly created objects [one in the list]
   *  Dest: the output
   */
  type MethodCall = (G, Option[EqClass], String, Changes[EqClass], Iterable[EqClass], G)

  def labeling(e: EqClass): String = e.toString
  
  type IGT2 = GT.ELGT{type V = G; type EL = MethodCall}
  type Interface = EdgeLabeledDiGraph[IGT2]

  def multiplicityToString(m: Multiplicity) = m match {
    case One => "one"
    case May => "may"
    case Part => "some"
    case Rest => "rest"
  }

  def objToString(obj: Obj): String = {
    val (tpe, ptsTo, unary, binary) = obj
    val flatBinary = for ( (p, fb) <- binary; (f,b) <- fb) yield (p,f,b)
    tpe +
    ptsTo.view.map{case (f, t) => f + " -> " + t}.mkString("(",", ",")") +
    unary.mkString("[",",","]") +
    flatBinary.mkString("{",",","}")
  }

  def simplify[A](b: Changes[A]): Changes[A] = {
    def simplify1(collec: Iterable[(Multiplicity, A)]): Iterable[(Multiplicity, A)] = {
      val (many, single) = collec.partition{ case (m, _) => m == Rest || m == Part }
      val byObj = many.groupBy(_._2)
      val many2 = byObj.map{ case (obj, lst) =>
        if (lst.exists(_._1 == Rest)) (Rest, obj) else (Part, obj)
      }
      single ++ many2
    }
    b.map{ case (a,b) => (a, simplify1(b))}
  }

  def loopAcceleration[A](becomes: Changes[A], eq: (A, A) => Boolean = ( (x:A,y:A) => x == y)): Changes[A] = {
    //println(becomes.mkString("\n"))
    for ( (src, dests) <- becomes ) yield {
      if (dests.size == 1) {
        Logger.assert(dests exists { case (m, v) => eq(v, src) && (m == Rest || m == One) }, "InterfaceExtraction", "frame not in dests: " + dests)
        (src, dests)
      } else if (dests.size == 2) {
        Logger.assert(dests exists { case (m, v) => eq(v, src) && m == Rest }, "InterfaceExtraction", "frame not in dests: " + dests)
        Logger.assert(dests exists { case (m, v) => m == One && !eq(v, src) }, "InterfaceExtraction", "dest not in dests: " + dests)
        //val res =  dests.map{ case (m, v) => if (eq(v, src)) (m,v) else (Part, v) }
        //println(dests.mkString(", "))
	//println(res.mkString(", "))
        (src, dests.map{ case (m, v) => if (eq(v, src)) (m,v) else (Part, v) })
      } else {
        Logger.logAndThrow("InterfaceExtraction", LogError, "expected loop with single dest + frame: " + dests)
      }
    }
  }

  def composeMultiplicities(m1: Multiplicity, m2: Multiplicity) = m1 match {
    case Rest => m2
    case Part => m2 match {
      case Rest => Part
      case _ => m2
    }
    case One => m2 match {
      case Rest | One => One
      case Part | May => May
    }
    case May => May
  }
    
  def compose[A](a: Changes[A], b: Changes[A]): Changes[A] = {
    //when not disjoint: One/May -> May, Rest/Part -> Part 
    val onlyB = b -- a.keys
    val a2 = a.map{ case (k, vs) => 
      (k, vs.flatMap{ case (m, v) =>
        b.getOrElse(v, Seq(Rest -> v)).map{ case (m2, v2) => (composeMultiplicities(m,m2), v2) }
      })
    }
    simplify(a2 ++ onlyB)
  }

  import picasso.utils.report._
  //pretty print the Interface
  def report(interface: Interface): Item = {
    import scala.text.Document
    import scala.text.Document._
    //collect the objects

    //val idsForObj = objs.zipWithIndex.map{ case (o, idx) => (o, "obj_"+idx) }.toMap

    def idsForObj(obj: Obj) = {
      val (tpe, ptsTo, unary, binary) = obj
      val flatBinary = for ( (p, fb) <- binary; (f,b) <- fb) yield (p,f,b)
      Misc.quote(
        "{ " + tpe + " | " +
        unary.map{ case (n,b) => if (b) n else "not " + n }.mkString(" | ") +
        flatBinary.mkString(" | ") +
        "}"
      )
    }

    val idsForCover = interface.vertices.iterator.zipWithIndex.map{ case (o, idx) => (o, "cover_"+idx) }.toMap
    val idsForTransitions = interface.edges.iterator.zipWithIndex.map{ case (t, idx) => (t._2, "t_"+idx) }.toMap

    def gToGv(g: G, id: String, kind: String = "digraph", misc: Document = empty): (Document, Map[EqClass, String]) = {
      g.toGraphvizExplicit(
        id, kind, misc, id,
        (node => List("label" -> idsForObj(node.obj), "shape" -> "record")),
        (edge => Nil)
      )
    }

    //a few graph to print:
    //-the structure of the automaton: give unique name to node and transition
    val outline = interface.toGraphvizExplicit(
        "outline",
        "digraph",
        scala.text.Document.empty,
        "outline",
        (node => List("label" -> idsForCover(node))),
        (edge => List("label" -> idsForTransitions(edge)))
      )._1
    //-the content of the nodes
    val nodesGraphs = idsForCover.map{ case (g, id) => (id, gToGv(g, id)._1) }
    //-the transitions
    val trsGraphs = idsForTransitions.map{ case ((from, caller, method, changes, news, to), id) =>
        val callerName = caller match {
          case Some(cl) => objToString(cl.obj)
          case None => "---"
        }
        val title = callerName + "." + method
        val (fromGv, fromNodesToId) = gToGv(from, "cluster_" + id + "_src", "subgraph", text("label = LHS;"))
        val (toGv, toNodesToId) = gToGv(to, "cluster_" + id + "_to", "subgraph", text("label = RHS;"))
        val changesEdges = changes.iterator.flatMap{ case (a, bs) => bs.map{ case (m, b) =>
            text( fromNodesToId(a) + " -> " + toNodesToId(b) + " [label=\""+ multiplicityToString(m) +"\"];")
          }
        }
        //TODO news
        val graphs = fromGv :/: toGv
        val body = (graphs /: changesEdges)(_ :/: _)
        (id, title, "digraph " :: id :: " {" :/: nest(4, body) :/: text("}"))
      }

    //pack everything into a report item.
    val top = new List("Interface")

    val outlineStr = Misc.docToString(outline)
    top.add(new GenericItem("Outline", outlineStr, Misc.graphvizToSvgDot(outlineStr)))

    val cover = new List("Cover")
    for ( (id, graph) <- nodesGraphs ) {
      val gv = Misc.docToString(graph)
      cover.add(new GenericItem(id, gv, Misc.graphvizToSvgDot(gv)))
    }
    top.add(cover)

    val trs = new List("Transitions")
    for ( (id, title, graph) <- trsGraphs ) {
      val gv = Misc.docToString(graph)
      trs.add(new GenericItem(id + ": " + title, gv, Misc.graphvizToSvgDot(gv)))
    }
    top.add(trs)

    top
  }

}

class InterfaceExtraction[P <: DBCT](proc: DepthBoundedProcess[P], cover: DownwardClosedSet[DepthBoundedConf[P]]) {
  import InterfaceExtraction._

  type DP = DepthBoundedConf[P]
  type DPV = (P#V, DepthBoundedConf[P])

  /* TODO language extraction from the transition graph (should go innto its own file)
   * assume transition name / comment are of the from  "methodName(thisType)[: newObj] [, comment]"
   * methods that do not have this shape are transient methods (from wich the result should be integrated in the first correctly named predecessor).
   *
   * 1st step: identifies the equivalence classes (object node with the predicates)
   * 2nd step: go along the edges (and morphing) while tracking the equivalence classes of this and the other objects
   * 3rd step: structure the output ...
   */

  /** Checks whether the system respects the assumption needed for the interface extraction. */
  def conforms: Boolean = {
    //TODO
    //method names
    //predicate / object names in the graph
    //type of transition
    //...
    sys.error("TODO")
  }

  val tg: EdgeLabeledDiGraph[TG[P]] = TransitionsGraphFromCover(proc, cover)

  protected def typeOf(node: P#V) = node.state.toString

  protected def isObj(node: P#V) = typeOf(node).head.isUpper //TODO this is an HACK!

  protected def isPred(node: P#V) = !isObj(node)

  protected def predValue(p: P#V): (String, Boolean) = {
    val nme = typeOf(p)
    if (nme startsWith "not_") (nme.substring(4), false)
    else (nme, true)
  }

  protected def isError(conf: DP) = {
    conf.vertices.exists(v => typeOf(v).endsWith("Error")) &&
    conf.vertices.forall(v => typeOf(v) != "safe")
  }
  
  protected def isTransient(conf: DP) = {
    conf.vertices.exists(v => typeOf(v).startsWith("transient")) &&
    conf.vertices.forall(v => typeOf(v) != "safe")
  }

  protected def eqClassToObj(cl: DPV): Obj = {
    //TODO the code for this method is really bad.
    //it can be made much faster, but since it is not a performance bottleneck ...

    Logger("InterfaceExtraction", LogDebug, "eqClassToObj: " + cl)

    val (node, graph) = cl
    val successors = graph(node)
    assert( (successors + node) == graph.vertices, "unrelated nodes in a DPV of " + node + "\n" + graph)
    val (objs, preds) = successors.partition(isObj)

    val objsWithField = objs.groupBy(o => {
      graph.outEdges(node).find{ case (k, v) => v contains o }.get._1
    }).map{ case (k, v) => (k.toString, v map typeOf) } 

    val (unaryPreds, binaryPreds) = preds.partition( p => {
      objs.forall(o => !graph(o).contains(p) ) //unary is pointed only by the node itself
    })

    val unaryValues = unaryPreds.map(predValue).toMap

    val binaryValues = binaryPreds.map( p => {
      val pointedBy = objs.filter(o => graph(o).contains(p) )
      assert(pointedBy.size == 1, pointedBy.mkString(", "))
      val other = pointedBy.head
      val field = graph.outEdges(node).find{ case (k, v) => v contains other }.get._1
      val (pName, v) = predValue(p)
      (pName, (typeOf(other), v))
    }).groupBy(_._1).map{ case (k, v) => (k, v.map(_._2).toMap ) }

    (typeOf(node), objsWithField, unaryValues, binaryValues)
  }

  protected def extractDPV(graph: DP, node: P#V): DPV = {
    Logger.assert(
        graph contains node,
        "InterfaceExtraction",
        "extractDPV: " + node + " is not in " + graph
      )
    val neighbors = graph(node).filter(isObj)
    val allPreds = graph(node).filter(isPred)
    val revG = graph.reverse
    val preds = allPreds.filter(p => {
      //val out = revG(p)
      //out.size == 1 || (out.size > 1 && neighbors.exists(out))
      true
    })
    //for the binary preds, keep only the pred if the other guy is a neighbor
    val keep = neighbors ++ preds + node
    val restricted = graph filterNodes keep
    //flatten to keep a single object.
    val height = node.depth
    if (height > 0) {
      val withLower = restricted.vertices.map(v => (v, (v /: (0 until math.max(0, v.depth - height)))( (v,_) => v-- ) ) )
      val morphing = withLower.toMap[P#V,P#V]
      (morphing(node), restricted morph morphing)
    } else {
      (node, restricted)
    }
  }

  protected def sameDPV(d1: DPV, d2: DPV): Boolean = {
    //check whether there is a morphism between d1 and d2 (compatible with the main obj)
    d1._2.morphisms(d2._2, Map(d1._1 -> d2._1))(proc.stateOrdering).hasNext &&
    d2._2.morphisms(d1._2, Map(d2._1 -> d1._1))(proc.stateOrdering).hasNext
  }

  protected lazy val eqClassesInGraph: Set[DPV] = {
    //get every object in every "non transient location" and trim the graph so that only the eq class is left.
    //a non transient location is a location of the cover (not all the location in tg).
    val objs = cover.flatMap( graph => {
      val objsNode = graph.vertices.filter(isObj)
      objsNode.map( n => extractDPV(graph, n) )
    })
    //remove the duplicates
    //first group by the node label so that we compare only objs of the same type
    val objByType = objs.groupBy( o => typeOf(o._1) )
    objByType.values.flatMap( sameType => {
      (Set[DPV]() /: sameType)( (acc, obj) => {
        if (acc.exists(sameDPV(obj, _)) ) acc else acc + obj
      })
    }).toSet
  }


  protected lazy val eqClassesMap: Map[DPV, Obj] = {
    eqClassesInGraph.iterator.map(conf => (conf, eqClassToObj(conf))).toMap
  }

  lazy val eqClasses: Set[Obj] = eqClassesMap.values.toSet

  protected def findClassOf(conf: DP, obj: P#V): DPV = {
    val extracted = extractDPV(conf, obj)
    val candidate = eqClassesInGraph.find( dpv => sameDPV(dpv, extracted))
    Logger.assert(
        candidate.isDefined,
        "InterfaceExtraction",
        "findClassOf: no candidate found for " + obj + "\n" + conf + extracted._1 + "\n" + extracted._2
      )
    candidate.get
  }


  protected def simpleTracking(curr: (Changes[P#V], List[P#V]), mapping: Map[P#V,P#V]) = {
    val (goesTo, news) = curr
    val goesToPrime = goesTo.map[(P#V, Iterable[(Multiplicity, P#V)]), Map[P#V, Iterable[(Multiplicity, P#V)]]]{ case (k,v) =>
      (k, v map {case (m, eq) => (m, mapping(eq))} )
    }
    val newsPrime = news map mapping
    (goesToPrime, newsPrime)
  }

  protected def track(curr: (Changes[P#V], List[P#V]), edge: TGEdges[P]): (Changes[P#V], List[P#V]) = edge match {
    case Transition(witness) => 
      //println("following transition: " + witness.transition.id)
      /// just in case ///
      witness.checkMorphisms
      witness.complete
      witness.checkMorphisms
      ////////////////////
      //unfolding (this one is reversed)
      val curr2 =
        if (witness.isUnfoldingTrivial) curr
        else {
          val mapping = witness.reversedUnfolding
          //node of highest depth is Rest, concrete is One, in between Part
          val (becomes, news) = curr
          val becomesPrime = becomes.map[(P#V, Iterable[(Multiplicity, P#V)]), Map[P#V, Iterable[(Multiplicity, P#V)]]]{ case (k,vs) =>
            (k, vs flatMap { case (m, v) =>
              val target = mapping(v)
              if (target.isEmpty) {
                Logger.logAndThrow("InterfaceExtraction", LogError, v.label + " disappears during the unfolding.")
              } else if (target.size == 1) {
                Seq(m -> target.head)
              } else {
                val highest = target.maxBy(_.depth)
                val (concrete, between) = target.view.filterNot(_ ==highest).partition(_.depth == 0)
                Logger.assert(between.forall(_.depth < highest.depth), "InterfaceExtraction", "multiple nodes with highest depth.")
                val highestM = m match {
                  case Rest => Rest
                  case Part => Part 
                  case _ => Logger.logAndThrow("InterfaceExtraction", LogError, "unfolding of concrete node !?")
                }
                val betweenM: Seq[(Multiplicity, P#V)] = between.map( Part -> _ )
                val concreteM: Seq[(Multiplicity, P#V)] = concrete.map ( One -> _ )
                val res: Seq[(Multiplicity, P#V)] = Seq(highestM -> highest) ++ betweenM ++ concreteM
                res
              }
            })
          }
          val newsPrime = news flatMap mapping
          (becomesPrime, newsPrime)
        }
      //inhibiting
      val curr3 =
        if (witness.isInhibitingTrivial) curr2
        else {
          Logger.logAndThrow("InterfaceExtraction", LogError, "TODO tracking of inhibitors")
        }
      //post
      val newNew = (witness.unfoldedAfterPost.vertices -- witness.post.values).filter(isObj)
      val (changed, newTracked) =
        if (witness.isPostTrivial) curr3
        else simpleTracking(curr3, witness.post)
      val curr4 = (changed, newTracked ++ newNew)
      //folding
      val curr5 =
        if (witness.isFoldingTrivial) curr4
        else simpleTracking(curr4, witness.folding)
      curr5
    case Covering(mapping) =>
      //println("following covering")
      simpleTracking(curr, mapping)
  }
  
  protected def follows(from: DP, trs: Seq[TGEdges[P]], to: DP): (Changes[P#V], Iterable[P#V]) = {
    //step 1: identify the objects in from
    val objsNode: Set[P#V] = from.vertices.filter(isObj)
    val iter: Iterator[(P#V, Seq[(Multiplicity, P#V)])] = objsNode.iterator.map(n => (n, Seq( (if (n.depth == 0) One else Rest) -> n)))
    val objsMap: Changes[P#V] = Map[P#V, Seq[(Multiplicity, P#V)]]() ++ iter
    val initTracking = (objsMap, List[P#V]())
    //step 2: follows that transition and keep track of the object identified in step 1 and the new objects
    val (goesTo, news) = (initTracking /: trs)(track)
    Logger.assert(goesTo.forall{ case (k,vs) => from.contains(k) && vs.forall(to contains _._2) },
                  "InterfaceExtraction",
                  "follows: goesTo has references to the wrong graph.")
    Logger.assert(news.forall(to contains _),
                  "InterfaceExtraction",
                  "follows: news has references to the wrong graph.")
    (goesTo, news)
  }
  
  /** decompose the transition graph into simple path going from cover location to cover location */
  protected def makePaths: Seq[(DP, Seq[TGEdges[P]], DP)] = {
    //the simple version
    val paths = tg.simplePaths
    Logger.assert(paths.forall(p => cover.contains(p.start) && cover.contains(p.stop)),
                  "InterfaceExtraction",
                  "TODO makePaths: a more complex way of spliting the paths ...")
    val paths2 = paths.view.flatMap(p => p.split(loc => cover.basis.contains(loc)))
    val paths3 = paths2.map(p => (p.start, p.labels, p.stop) )
    paths3.force
  }

  /** methodName(thisType)[: newObj] [, comment]
   *  returns (thisType, methodName, [newObj])
   */
  protected def parseName(str: String): Option[(String,String,Option[String])] = {
    val woComment =
      if (str.indexOf(",") == -1) str
      else str.substring(0, str.indexOf(","))
    try {
      val lparen = woComment.indexOf("(")
      val rparen = woComment.indexOf(")")
      val methodName = woComment.substring(0, lparen)
      val tpe = woComment.substring(lparen + 1, rparen)
      val rest = woComment.substring(rparen + 1)
      val created =
        if (rest contains ":") Some(rest.substring(rest.indexOf(":") + 1).trim)
        else None
      Some((tpe, methodName, created))
    } catch {
      case e: java.lang.StringIndexOutOfBoundsException =>
        None
    }
  }

  // parse the comment from the transition to get the method name and the type/id of the caller
  protected def parseTransition(edge: TGEdges[P]): (Option[P#V], String, Option[ObjType]) = edge match {
    case Transition(witness) =>
      Logger("InterfaceExtraction", LogInfo, "making edge for: " + witness.transition.id)
      parseName(witness.transition.id) match {
        case Some((tpe, call, created)) =>
          //println("looking for candidate of type " + tpe + " in " + witness.modifiedPre.map(typeOf).mkString(", "))
          val candidates = witness.modifiedPre.filter(n => typeOf(n) == tpe)
          if (candidates.isEmpty) {
            Logger("InterfaceExtraction", LogWarning, "pathToMethodCall: no candidates")
            (None, call, created)
          } else {
            if (candidates.size > 1) {
              Logger( "InterfaceExtraction",
                      LogWarning,
                      "pathToMethodCall: more than one candidate for \""+witness.transition.id+"\": " + candidates.mkString(", ")
                    )
            }
            (Some(candidates.head), call, created)
          }
        case None =>
          Logger("InterfaceExtraction", LogWarning, "pathToMethodCall: cannot parse \""+witness.transition.id+"\"")
          (None, "---", None)
      }
    case _ => Logger.logAndThrow("InterfaceExtraction", LogError, "pathToMethodCall: expected Transition")
  }

  protected def removePreds(conf: DP): (G, Map[P#V, EqClass]) = {
    val (objNode, predNodes) = conf.vertices.partition(isObj)
    val nodeTObj = objNode.iterator.map( v => (v, new EqClass( eqClassToObj(findClassOf(conf,v)))) ).toMap[P#V, EqClass]
    val objOnly = conf -- predNodes
    //cannot use morphism because it is not the same kind of GraphLike.
    //thus, we take it appart, convert, and rebuild it.
    val eqClasses = nodeTObj.values
    val edges = objOnly.edges.map{ case (a, b, c) => (nodeTObj(a), b.toString, nodeTObj(c)) }
    (LabeledDiGraph[IGT](edges, labeling(_)).addVertices(eqClasses), nodeTObj)
  }
  
  type MethodCallWithMaps = ( MethodCall, Map[P#V, EqClass], Map[P#V, EqClass])
  
  /* on top of the method call, it also returns srcMap and dstMap */
  protected def pathToMethodCall2(path: (DP, Seq[TGEdges[P]], DP)): MethodCallWithMaps = {
    //MethodCall = (G, EqClass, String, Changes[EqClass], Iterable[EqClass], G)
    //(1) parse the comment from the transition to get the method name and the type/id of the caller
    val (obj, method, createdTpe) = parseTransition(path._2.head)
    //(2) follows
    val (becomes, news) = follows(path._1, path._2, path._3)
    if (createdTpe.size != news.size) {
      Logger( "InterfaceExtraction",
              LogWarning,
              "pathToMethodCall: wrong number of created objects ?! " + createdTpe + " vs " + news.mkString("[",",","]"))
    }
    //(3) convert src and dest =
    val (src, srcMap) = removePreds(path._1)
    val (dst, dstMap) = removePreds(path._3)
    //(3) put things together
    val becomesObj = simplify(becomes.map{ case (k,vs) => (srcMap(k), vs map { case (m, cl) => (m, dstMap(cl)) } ) })
    val newsObj = news map dstMap 
    //checkChangesDomains("pathToMethodCall.becomesObj", src, becomesObj, dst)
    //Logger.assert(srcMap.values.forall(src contains _), "InterfaceExtraction", "pathToMethodCall.srcMap")
    //Logger.assert(dstMap.values.forall(dst contains _), "InterfaceExtraction", "pathToMethodCall.dstMap")
    val call = (src, obj map srcMap, method, becomesObj, newsObj, dst)
    (call, srcMap, dstMap)
  }

  private def checkChangesDomains(what: String, from: G, c: Changes[EqClass], to: G) {
    Logger.assert(c.keys.forall(from contains _), "InterfaceExtraction", what + ": src not in graph")
    Logger.assert(c.values.forall(_.forall(to contains _._2)), "InterfaceExtraction", what + ": dest not in graph")
  }
  
  protected def composeTransition(t1: MethodCallWithMaps, middle: DP, t2: MethodCallWithMaps): MethodCallWithMaps = {
    //println("composeTransition ...")
    val ((t1From, t1Caller, t1Method, t1Changes, t1News, t1To), t1Src, t1Dest) = t1
    //checkChangesDomains("composeTransition.t1", t1From, t1Changes, t1To)
    //Logger.assert(t1Src.values.forall(t1From contains _), "InterfaceExtraction", "pathToMethodCall.t1Src")
    //Logger.assert(t1Dest.values.forall(t1To contains _), "InterfaceExtraction", "pathToMethodCall.t1Dest")
    val ((t2From, t2Caller, t2Method, t2Changes, t2News, t2To), t2Src, t2Dest) = t2
    //checkChangesDomains("composeTransition.t2", t2From, t2Changes, t2To)
    //Logger.assert(t2Src.values.forall(t2From contains _), "InterfaceExtraction", "pathToMethodCall.t2Src")
    //Logger.assert(t2Dest.values.forall(t2To contains _), "InterfaceExtraction", "pathToMethodCall.t2Dest")
    //need to compute: x => t2Src(t1Dest^{-1}(x))
    val t1DestInverse = t1Dest.map[(EqClass,P#V), Map[EqClass, P#V]]{ case (a,b) => (b,a) }
    //Logger.assert(t1DestInverse.keys.forall(t1To contains _), "InterfaceExtraction", "pathToMethodCall.t1DestInverse")
    def t1ToT2(x: EqClass) = t2Src(t1DestInverse(x))
    //val t2SrcInverse = t2Src.map[(EqClass,P#V), Map[EqClass, P#V]]{ case (a,b) => (b,a) }
    //val t2ToT1(x: EqClass) = t2Dest(t2SrcInverse(x))
    //and compose with t2 
    val resChanges = t1Changes.map{ case (a, bs) => (a, bs.flatMap{ case (m, b) =>
        t2Changes(t1ToT2(b)).map{ case (m2, b2) => (composeMultiplicities(m, m2), b2) }
      })
    }
    //assert(t2Changes.keys.forall(k => t1Changes.values.exists(_.exists(c => t1ToT2(c._2) == k))))
    //val t1Range = t1Changes.values.flatMap(_.map(_._2)).toSet.map(t1ToT2)
    //val newChanges = t2Changes.filterNot(t1Range)
    //val resChangesPart2 =  newChanges.map{ case (a, bs) => (t1DstToSrc(a), bs) }
    //val resChanges =
    val resNews = t1News.flatMap( n => t2Changes(t1ToT2(n)).map(_._2) )
    checkChangesDomains("composeTransition.resChanges", t1From, resChanges, t2To)
    Logger.assert(resNews.forall(t2To contains _), "InterfaceExtraction", "composeTransition: news not in graph")
    ((t1From, t1Caller, t1Method, resChanges, resNews, t2To), t1Src, t2Dest)
  }

  protected def accelerateIfNeeded(start: DP, call: MethodCallWithMaps, end: DP): MethodCallWithMaps = {
    if (start == end) {
      val ((from, caller, method, changes, news, to), src, dest) = call
      Logger.assert(news.isEmpty, "InterfaceExtraction", "TODO new object and acceleration")
      val accelerated = loopAcceleration(changes, (x: EqClass, y: EqClass) => x.obj == y.obj)
      Logger.assert(accelerated.keys.forall(from contains _), "InterfaceExtraction", "accelerated: src not in graph")
      Logger.assert(accelerated.values.forall(_.forall(to contains _._2)), "InterfaceExtraction", "accelerated: dest not in graph")
      ((from, caller, method, accelerated, news, to), src, dest)
    } else {
      call
    }
  }

  protected def compactPath(trace: Trace[DP, MethodCallWithMaps]): (DP, MethodCallWithMaps, DP) = {
    //accelerate when needed and fold over the trace
    Logger.assert(trace.length >= 1, "InterfaceExtraction", "trace is empty")
    val (fstCall, middle) = trace.head
    val call = accelerateIfNeeded(trace.start, fstCall, middle)
    val (finalCall, _) = ((call, middle) /: trace.tail)( (acc, step) => {
      val aCall = accelerateIfNeeded(acc._2, step._1, step._2)
      (composeTransition(acc._1, acc._2, aCall), step._2)
    })
    val (start, end) = trace.extremities
    (start, finalCall, end)
  }

  def pruneCall(call: MethodCall): MethodCall = {
    val (src, caller, method, changes, news, dst) = call
    val changes2 = changes.filterNot{ case (a,bs) => 
      if (a != caller && bs.size == 1) {
        val (m, b) = bs.head
        (m == Rest && b.obj == a.obj)
      } else false
    }
    val src2 = src.filterNodes(n => n == caller || changes2.keySet(n))
    val changesRange = changes2.values.flatMap(_.map(_._2)).toSet
    val newsSet = news.toSet
    val dst2 = dst.filterNodes(n => newsSet(n) || changesRange(n) )
   (src2, caller, method, changes2, news, dst2)
  }

  def interface: Interface = {
    Logger("InterfaceExtraction", LogNotice, "Extracting interface ...")
    if (Logger("InterfaceExtraction", LogDebug)) {
      val structure = TransitionsGraphFromCover.structureToGraphviz(cover, tg)
      Logger("InterfaceExtraction", LogDebug, Misc.docToString(structure))
    }

    val edges: Iterable[(DP, MethodCallWithMaps, DP)] = makePaths.map(path => (path._1, pathToMethodCall2(path), path._3) )
    val withTransient = EdgeLabeledDiGraph[GT.ELGT{type V = DP; type EL = MethodCallWithMaps}](edges).addVertices(cover.basis.seq)
    val transientStates = withTransient.vertices.filter(isTransient)
    val revWithTransient = withTransient.reverse

    Logger("InterfaceExtraction", LogInfo, "removing transient paths")
    //includes the self loops
    def mkTransientPath(t: DP): Iterable[Trace[DP, MethodCallWithMaps]] = {
      val prefixes = for( (preLabel, preDest) <- revWithTransient.outEdges(t);
                          pre <- preDest if !isTransient(pre))
                     yield (pre, preLabel)
      def recurse(current: DP, seen: Set[DP]): Iterable[Trace[DP,MethodCallWithMaps]] = {
        if (!isTransient(current)) {
          Seq(new Trace[DP, MethodCallWithMaps](current, Nil))
        } else {
          val seen2 = seen + current
          val after = for ((label, nexts) <- withTransient.outEdges(current);
               next <- nexts if !seen2(next);
               suffix <- recurse(next, seen2) ) yield {
            suffix.prepend(current, label)
          }
          val selfLoop = withTransient.edgesBetween(current,current)
          after.map(trc => (trc /: selfLoop)( (acc, loop) => acc.prepend(current, loop) ) )
        }
      }
      val suffixes = recurse(t, Set[DP]())
      prefixes.flatMap{ case (start, call) => suffixes.map(_.prepend(start, call)) }
    }

    val pathsSummarized = transientStates.iterator.flatMap( mkTransientPath ).map( compactPath )

    val withoutTransient = withTransient -- transientStates ++ pathsSummarized.toTraversable

    val dict = withTransient.vertices.iterator.map( c => (c, removePreds(c)._1) ).toMap

    val interface = withoutTransient.morphFull[IGT2](
        dict,
        (el => pruneCall(el._1)),
        (x => x)
      )

    interface
  }
}
