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

  type Become = Map[Obj, Iterable[(Multiplicity, Obj)]]

  /** What happens each time a method is called.
   *  Obj: the caller
   *  String: the method name
   *  Become: what an object becomes / might become
   *  Iterable[Obj]: the newly created objects
   */
  type MethodCall = (Obj, String, Become, Iterable[Obj])

  type IGT = GT.ELGT{type V = String; type EL = MethodCall}

  type Interface = EdgeLabeledDiGraph[IGT]

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

  protected def callToStringAux(call: MethodCall, objPrint: Obj => String): String = {
    val (obj, method, becomes, created) = call
    val flatBecomes = for ( (o1, set) <- becomes; (m,o2) <- set) yield (m,o1,o2)
    objPrint(obj) + "." + method +
    flatBecomes.view.map{ case (m,o1,o2) => multiplicityToString(m) + " " + objPrint(o1) + " -> " + objPrint(o2) }.mkString("(",", ",")") +
    created.map(objPrint).mkString(", ")
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
      acc + obj ++ becomes.keys ++ becomes.values.flatMap(_.map(_._2)) ++ created
    })
    val dict = objs.zipWithIndex.map{ case (o, idx) => (o, "cl_"+idx) }.toMap
    val gv = interface.toGraphvizExplicit(
        "interface",
        "digraph",
        scala.text.Document.empty,
        "interface",
        (node => List("label" -> Misc.quote(node))),
        (edge => List("label" -> Misc.quote(callToStringShort(dict, edge))))
      )._1
    (dict, gv)
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
    val keep = graph(node) + node
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


  protected def simpleTracking(curr: (Map[P#V, Seq[(Multiplicity, P#V)]], List[P#V]), mapping: Map[P#V,P#V]) = {
    val (goesTo, news) = curr
    val goesToPrime = goesTo.map[(P#V, Seq[(Multiplicity, P#V)]), Map[P#V, Seq[(Multiplicity, P#V)]]]{ case (k,v) =>
      (k, v map {case (m, eq) => (m, mapping(eq))} )
    }
    val newsPrime = news map mapping
    (goesToPrime, newsPrime)
  }

  protected def track(curr: (Map[P#V, Seq[(Multiplicity, P#V)]], List[P#V]), edge: TGEdges[P]): (Map[P#V, Seq[(Multiplicity, P#V)]], List[P#V]) = edge match {
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
          val becomesPrime = becomes.map[(P#V, Seq[(Multiplicity, P#V)]), Map[P#V, Seq[(Multiplicity, P#V)]]]{ case (k,vs) =>
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
  
  protected def follows(from: DP, trs: Seq[TGEdges[P]], to: DP): (Map[DPV, Seq[(Multiplicity, DPV)]], Iterable[DPV]) = {
    //step 1: identify the objects in from
    val objsNode: Set[P#V] = from.vertices.filter(isObj)
    val iter: Iterator[(P#V, Seq[(Multiplicity, P#V)])] = objsNode.iterator.map(n => (n, Seq( (if (n.depth == 0) One else Rest) -> n)))
    val objsMap = Map[P#V, Seq[(Multiplicity, P#V)]]() ++ iter
    val initTracking = (objsMap, List[P#V]())
    //step 2: follows that transition and keep track of the object identified in step 1 and the new objects
    val (goesTo, news) = (initTracking /: trs)(track)
    Logger.assert(goesTo.forall{ case (k,vs) => from.contains(k) && vs.forall(to contains _._2) },
                  "InterfaceExtraction",
                  "follows: goesTo has references to the wrong graph.")
    Logger.assert(news.forall(to contains _),
                  "InterfaceExtraction",
                  "follows: news has references to the wrong graph.")
    //step 3: map the objects to their equivalence classes
    val newsDpv = news.map(x => findClassOf(to, x) )
    val goesToDpv = goesTo.map{case (k, vs) => (findClassOf(from, k), vs.map{ case(m, v) => (m, findClassOf(to, v))}) }
    //step 4: trim (remove the unchanged objects)
    val trimedGoesTo = goesToDpv.filterNot{ case (k, vs) => vs.size == 1 && (vs.exists(_._2 == k)) }
    (trimedGoesTo, newsDpv)
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

  protected def pathToMethodCall(path: (DP, Seq[TGEdges[P]], DP)): MethodCall = {
    //MethodCall = (Obj, String, Map[Obj, Set[Obj]], Iterable[Obj])
    //(1) parse the comment from the transition to get the method name and the type/id of the caller
    val (obj, method, createdTpe) = path._2.head match {
      case Transition(witness) =>
        Logger("InterfaceExtraction", LogInfo, "making edge for: " + witness.transition.id)
        parseName(witness.transition.id) match {
          case Some((tpe, call, created)) =>
            //println("looking for candidate of type " + tpe + " in " + witness.modifiedPre.map(typeOf).mkString(", "))
            val candidates = witness.modifiedPre.filter(n => typeOf(n) == tpe)
            if (candidates.isEmpty) {
              Logger("InterfaceExtraction", LogWarning, "pathToMethodCall: no candidates")
              (("unknown", Map.empty, Map.empty, Map.empty): Obj, "---", None)
            } else {
              if (candidates.size > 1) {
                Logger( "InterfaceExtraction",
                        LogWarning,
                        "pathToMethodCall: more than one candidate for \""+witness.transition.id+"\": " + candidates.mkString(", ")
                      )
              }
              val cnd = candidates.head
              val dpv = findClassOf(path._1, cnd)
              (eqClassesMap(dpv), call, created)
            }
          case None =>
            Logger("InterfaceExtraction", LogWarning, "pathToMethodCall: cannot parse \""+witness.transition.id+"\"")
            (("unknown", Map.empty, Map.empty, Map.empty): Obj, "---", None)
        }
      case _ => Logger.logAndThrow("InterfaceExtraction", LogError, "pathToMethodCall: expected Transition")
    }

    //(2) follows
    val (becomes, news) = follows(path._1, path._2, path._3)
    if (createdTpe.size != news.size) {
      Logger( "InterfaceExtraction",
              LogWarning,
              "pathToMethodCall: wrong number of created objects ?! " + createdTpe + " vs " + news.mkString("[",",","]"))
    }
    //(3) put things together
    val becomesObj = becomes.map{ case (k,vs) => (eqClassesMap(k), vs map { case (m, cl) => (m, eqClassesMap(cl)) } ) }
    val newsObj = news map eqClassesMap
    (obj, method, simplify(becomesObj), newsObj)
  }

  protected def simplify(b: Become): Become = {
    def simplify1(collec: Iterable[(Multiplicity, Obj)]): Iterable[(Multiplicity, Obj)] = {
      val (many, single) = collec.partition{ case (m, _) => m == Rest || m == Part }
      val byObj = many.groupBy(_._2)
      val many2 = byObj.map{ case (obj, lst) =>
        if (lst.exists(_._1 == Rest)) (Rest, obj) else (Part, obj)
      }
      single ++ many2
    }
    b.map{ case (a,b) => (a, simplify1(b))}
  }


  //post-processing to remove the transient states
  //TODO this part is ugly, needs some refactoring
  protected def removeTransientLoops(it: Interface): Interface = {
    def transient(s: String) = s.startsWith("transient")

    def compose(a: Become, b: Become): Become = {
      def mult(m1: Multiplicity, m2: Multiplicity) = m1 match {
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
      //when not disjoint: One/May -> May, Rest/Part -> Part 
      val onlyB = b -- a.keys
      val a2 = a.map{ case (k, vs) => 
        (k, vs.flatMap{ case (m, v) =>
          b.getOrElse(v, Seq(Rest -> v)).map{ case (m2, v2) => (mult(m,m2), v2) }
        })
      }
      simplify(a2 ++ onlyB)
    }

    val transientStates = it.vertices.filter(transient)
    val revIt = it.reverse

    def selfLoopAcceleration(becomes: Become): Become = {
      for ( (src, dests) <- becomes ) yield {
        Logger.assert(dests.size == 2, "InterfaceExtraction", "expected loop with single dest + frame: " + dests)
        Logger.assert(dests exists { case (m, v) => v == src && m == Rest }, "InterfaceExtraction", "frame not in dests: " + dests)
        Logger.assert(dests exists { case (m, v) => m == One && v != src }, "InterfaceExtraction", "dest not in dests: " + dests)
        (src, dests.map{ case (m, v) => if (v == src) (m,v) else (Part, v) })
      }
    }

    //includes the self loops
    def mkPath(t: String): Iterable[Trace[String, MethodCall]] = {
      val prefixes = for( (preLabel, preDest) <- revIt.outEdges(t); pre <- preDest if !transient(pre)) yield (pre, preLabel)
      def recurse(current: String, seen: Set[String]): Iterable[Trace[String,MethodCall]] = {
        if (!transient(current)) {
          Seq(new Trace[String, MethodCall](current, Nil))
        } else {
          val seen2 = seen + current
          val after = for ((label, nexts) <- it.outEdges(current);
               next <- nexts if !seen2(next);
               suffix <- recurse(next, seen2) ) yield {
            suffix.prepend(current, label)
          }
          val selfLoop = it.edgesBetween(current,current)
          after.map(trc => (trc /: selfLoop)( (acc, loop) => acc.prepend(current, loop) ) )
        }
      }
      val suffixes = recurse(t, Set[String]())
      prefixes.flatMap{ case (start, call) => suffixes.map(_.prepend(start, call)) }
    }

    val pathsToSummarize = transientStates.iterator.flatMap( mkPath )

    val paths: Iterator[(String, MethodCall, String)] = for ( trace <- pathsToSummarize) yield {
      val (obj, method, _, _) = trace.labels.head
      val initCall: MethodCall = (obj, method, Map.empty, Nil)
      val (_, call) = ( (trace.start, initCall) /: trace)( (acc, next) => {
        val (src, (obj1, method1, becomes1, news1)) = acc
        val ((obj2, method2, becomes2, news2), trgt) = next
        Logger.assert((obj2._1 == "unknown" || obj2 == obj1) &&
                      (method2 == "---" || method2 == method1) &&
                      news2.isEmpty,
                      "InterfaceExtraction",
                      "transient edge not as expected " + next)
        val becomes3 = if (src == trgt) selfLoopAcceleration(becomes2) else becomes2
        (trgt, (obj1, method1, compose(becomes1, becomes3), news1))
      })
      val (start, end) = trace.extremities
      (start, call, end)
    }
    it -- transientStates ++ paths.toTraversable
  }

  def interface: Interface = {
    Logger("InterfaceExtraction", LogNotice, "Extracting interface ...")
    if (Logger("InterfaceExtraction", LogDebug)) {
      val structure = TransitionsGraphFromCover.structureToGraphviz(cover, tg)
      Logger("InterfaceExtraction", LogDebug, Misc.docToString(structure))
    }
    def nameConf(c: DP) = {
      if (isError(c)) Namer("error")
      else if (isTransient(c)) Namer("transient")
      else Namer("cover")
    }
    val edges: Iterable[(DP, MethodCall, DP)] = makePaths.map(path => (path._1, pathToMethodCall(path), path._3) )
    val nodes = cover.basis.seq
    val names = nodes.map( c => (c, nameConf(c)) ).toMap
    val edgesWithStr = edges.map{ case (a,b,c) => (names(a), b, names(c)) }
    val withTransient = EdgeLabeledDiGraph[IGT](edgesWithStr).addVertices(nodes map names)
    removeTransientLoops(withTransient)
  }

}
