package picasso.analysis

import picasso.utils._
import picasso.model.dbp._
import picasso.graph._
import picasso.math._
import TransitionsGraphFromCover._

object InterfactExtraction {

  type ObjType = String
  type Field = String
  type UnaryPredicates = Map[String, Boolean]
  type BinaryPredicates = Map[String, Map[Field,Boolean]]
  //obj: class name, neighborhood (to what it is connected), unary predicates, binary predicates
  type Obj = (ObjType, Map[Field, Iterable[ObjType]], UnaryPredicates, BinaryPredicates)

  //types for the transitions and the language

  /** What happens each time a method is called.
   *  Obj: the caller
   *  String: the method name
   *  Map[Obj, Set[Obj]]: what an object becomes / might become
   *  Iterable[Obj]: the newly created objects
   */
  type MethodCall = (Obj, String, Map[Obj, Set[Obj]], Iterable[Obj])

  type IGT = GT.ELGT{type V = String; type EL = MethodCall}

  type Interface = EdgeLabeledDiGraph[IGT]

  def objToString(obj: Obj): String = {
    val (tpe, ptsTo, unary, binary) = obj
    val flatBinary = for ( (p, fb) <- binary; (f,b) <- fb) yield (p,f,b)
    tpe +
    ptsTo.view.map{case (f, t) => f + " -> " + t}.mkString("(",", ",")") +
    unary.mkString("[",",","]") +
    flatBinary.mkString("{",",","}")
  }

  protected def callToStringAux(call: MethodCall, objPrint: Obj => String): String = {
    val (obj, method, becomes, created) = call
    val flatBecomes = for ( (o1, set) <- becomes; o2 <- set) yield (o1,o2)
    objPrint(obj) + "." + method +
    flatBecomes.view.map{ case (o1,o2) => objPrint(o1) + " -> " + objPrint(o2) }.mkString("(",", ",")") +
    created.mkString(", ")
  }
  
  def callToString(call: MethodCall): String = {
    callToStringAux(call, objToString)
  }
  
  def callToStringShort(dict: Map[Obj, String], call: MethodCall): String = {
    callToStringAux(call, dict)
  }

  def interfaceToGV(interface: Interface): (Map[Obj, String], scala.text.Document) = {
    val objs = (Set[Obj]() /: interface.edges)( (acc, call) => {
      val (_, (obj,_,becomes,created), _) = call
      acc + obj ++ becomes.keys ++ becomes.values.flatten ++ created
    })
    val dict = objs.zipWithIndex.map{ case (o, idx) => (o, "eq_cl_"+idx) }.toMap
    val gv = interface.toGraphvizExplicit(
        "interface",
        "digraph",
        scala.text.Document.empty,
        "interface",
        (node => List("label" -> Misc.quoteIfFancy(node))),
        (edge => List("label" -> Misc.quoteIfFancy(callToStringShort(dict, edge))))
      )._1
    (dict, gv)
  }

}

class InterfactExtraction[P <: DBCT](proc: DepthBoundedProcess[P], cover: DownwardClosedSet[DepthBoundedConf[P]]) {
  import InterfactExtraction._

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
    if (nme startsWith "not_") (nme.substring(4), true)
    else (nme, false)
  }

  protected def eqClassToObj(cl: DPV): Obj = {
    //TODO the code for this method is really bad.
    //it can be made much faster, but since it is not a performance bottleneck ...

    Logger("InterfactExtraction", LogDebug, "eqClassToObj: " + cl)

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
        "InterfactExtraction",
        "extractDPV: " + node + " is not in " + graph
      )
    val keep = graph(node) + node
    val restricted = graph filterNodes keep
    //flatten to keep a single object.
    val height = node.depth
    if (height > 0) {
      val withLower = restricted.vertices.map(v => (v, (v /: (0 until math.max(0, v.depth - height)))( (v,_) => v-- ) ) )
      val morphing = withLower.toMap[P#V,P#V]
      (morphing(node), restricted morph morphing) //TODO key not found: picasso.model.dbp.Thread@52c00025-(Iter,1)
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
        "InterfactExtraction",
        "findClassOf: no candidate found for " + obj + "\n" + conf + extracted._1 + "\n" + extracted._2
      )
    candidate.get
  }


  //TODO track a node along a transition: need some modifiers All, Some, 1, AllBut(List[Modifiers])

  protected def simpleTracking(curr: (Map[P#V, Set[P#V]], List[P#V]), mapping: Map[P#V,P#V]) = {
    val (goesTo, news) = curr
    val goesToPrime = goesTo.map[(P#V, Set[P#V]), Map[P#V, Set[P#V]]]{case (k,v) => (k, v map mapping)} //TODO key not found: picasso.model.dbp.Thread@79b4748-(Iter,0)
    val newsPrime = news map mapping
    (goesToPrime, newsPrime)
  }

  protected def track(curr: (Map[P#V, Set[P#V]], List[P#V]), edge: TGEdges[P]): (Map[P#V, Set[P#V]], List[P#V]) = edge match {
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
          (curr._1.map[(P#V, Set[P#V]), Map[P#V, Set[P#V]]]{case (k,v) => (k, v flatMap mapping)}, curr._2 flatMap mapping)
        }
      //inhibiting
      val curr3 =
        if (witness.isInhibitingTrivial) curr2
        else {
          Logger.logAndThrow("InterfactExtraction", LogError, "TODO tracking of inhibitors")
        }
      //post
      val curr4 =
        if (witness.isPostTrivial) curr3
        else simpleTracking(curr3, witness.post)
      //folding
      val curr5 =
        if (witness.isFoldingTrivial) curr4
        else simpleTracking(curr4, witness.folding)
      curr5
    case Covering(mapping) =>
      //println("following covering")
      simpleTracking(curr, mapping)
  }
  
  protected def follows(from: DP, trs: Seq[TGEdges[P]], to: DP): (Map[DPV, Set[DPV]], Iterable[DPV]) = {
    //step 1: identify the objects in from
    val objsNode: Set[P#V] = from.vertices.filter(isObj)
    val iter: Iterator[(P#V, Set[P#V])] = objsNode.iterator.map(n => (n, Set(n)))
    val objsMap = Map[P#V, Set[P#V]]() ++ iter
    val initTracking = (objsMap, List[P#V]())
    //step 2: follows that transition and keep track of the object identified in step 1 and the new objects
    val (goesTo, news) = (initTracking /: trs)(track)
    Logger.assert(goesTo.forall{ case (k,vs) => from.contains(k) && vs.forall(to contains _) },
                  "InterfactExtraction",
                  "follows: goesTo has references to the wrong graph.")
    Logger.assert(news.forall(to contains _),
                  "InterfactExtraction",
                  "follows: news has references to the wrong graph.")
    //step 3: map the objects to their equivalence classes
    val newsDpv = news.map(x => findClassOf(to, x) )
    val goesToDpv = goesTo.map{case (k, vs) => (findClassOf(from, k), vs.map(v => findClassOf(to, v))) }
    //step 4: trim (remove the unchanged objects)
    val trimedGoesTo = goesToDpv.filterNot{ case (k, vs) => vs.size == 1 && (vs contains k) }
    (trimedGoesTo, newsDpv)
  }

  /** decompose the transition graph into simple path going from cover location to cover location */
  protected def makePaths: Seq[(DP, Seq[TGEdges[P]], DP)] = {
    //the simple version
    val paths = tg.simplePaths
    Logger.assert(paths.forall(p => cover.contains(p.start) && cover.contains(p.stop)),
                  "InterfactExtraction",
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

  protected def pathToMethodCall(path: (DP, Seq[TGEdges[P]], DP)): MethodCall = {
    //MethodCall = (Obj, String, Map[Obj, Set[Obj]], Iterable[Obj])
    //(1) parse the comment from the transition to get the method name and the type/id of the caller
    val (obj, method, createdTpe) = path._2.head match {
      case Transition(witness) =>
        Logger("InterfactExtraction", LogInfo, "making edge for: " + witness.transition.id)
        parseName(witness.transition.id) match {
          case Some((tpe, call, created)) =>
            println("looking for candidate of type " + tpe + " in " + witness.modifiedPre.map(typeOf).mkString(", "))
            val candidates = witness.modifiedPre.filter(n => typeOf(n) == tpe)
            if (candidates.isEmpty) {
              Logger("InterfactExtraction", LogWarning, "pathToMethodCall: no candidates")
              (("unknown", Map.empty, Map.empty, Map.empty): Obj, "---", None)
            } else {
              if (candidates.size > 1) {
                Logger( "InterfactExtraction",
                        LogWarning,
                        "pathToMethodCall: more than one candidate for \""+witness.transition.id+"\": " + candidates.mkString(", ")
                      )
              }
              val cnd = candidates.head
              val dpv = findClassOf(path._1, cnd)
              (eqClassesMap(dpv), call, created)
            }
          case None =>
            Logger("InterfactExtraction", LogWarning, "pathToMethodCall: cannot parse \""+witness.transition.id+"\"")
            (("unknown", Map.empty, Map.empty, Map.empty): Obj, "---", None)
        }
      case _ => Logger.logAndThrow("InterfactExtraction", LogError, "pathToMethodCall: expected Transition")
    }

    //(2) follows
    val (becomes, news) = follows(path._1, path._2, path._3)
    if (createdTpe.size != news.size) {
      Logger( "InterfactExtraction",
              LogWarning,
              "pathToMethodCall: wrong number of created objects ?! " + createdTpe + " vs " + news.mkString("[",",","]"))
    }
    //(3) put things together
    val becomesObj = becomes.map{ case (k,vs) => (eqClassesMap(k), vs map eqClassesMap) }
    val newsObj = news map eqClassesMap
    (obj, method, becomesObj, newsObj)
  }

  def interface: Interface = {
    Logger("InterfactExtraction", LogNotice, "Extracting interface ...")
    if (Logger("InterfactExtraction", LogDebug)) {
      val structure = TransitionsGraphFromCover.structureToGraphviz(cover, tg)
      Logger("InterfactExtraction", LogDebug, Misc.docToString(structure))
    }
    val edges: Iterable[(DP, MethodCall, DP)] = makePaths.map(path => (path._1, pathToMethodCall(path), path._3) )
    val nodes = cover.basis.seq
    val names = nodes.map( c => (c, Namer("cover")) ).toMap
    val edgesWithStr = edges.map{ case (a,b,c) => (names(a), b, names(c)) }
    EdgeLabeledDiGraph[IGT](edgesWithStr).addVertices(nodes map names)
  }

}
