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

  //use DepthBoundedConf to preserve the depth
  type IGT = DBCT{type State = Obj; type EL = String}
  type G = DepthBoundedConf[IGT]

  /** What happens each time a method is called.
   *  Src: the input
   *  Role: maps some nodes to their role in the fct call (callee, args, ...)
   *  String: the method name
   *  Become: what an object becomes / might become
   *  Iterable[Obj]: the newly created objects [one in the list]
   *  Dest: the output
   */
  type MethodCall = (G, Map[G#V, String], String, Changes[G#V], Iterable[G#V], G)

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
 

  /** methodName(thisType {, argType}* )[: newObj] [; comment]
   *  returns (thisType, methodName, argsTypes, [newObj])
   */
  def parseTransitionName(str: String): Option[(ObjType, String, Seq[ObjType], Option[ObjType])] = {
    val woComment =
      if (str.indexOf(";") == -1) str
      else str.substring(0, str.indexOf(";"))
    try {
      val lparen = woComment.indexOf("(")
      val rparen = woComment.indexOf(")")
      val methodName = woComment.substring(0, lparen)
      val tpes = woComment.substring(lparen + 1, rparen).split(",").map(_.trim)
      val rest = woComment.substring(rparen + 1)
      val created =
        if (rest contains ":") Some(rest.substring(rest.indexOf(":") + 1).trim)
        else None
      Some((tpes.head, methodName, tpes.tail, created))
    } catch {
      case e: java.lang.StringIndexOutOfBoundsException =>
        None
    }
  }

  import picasso.utils.report._
  //pretty print the Interface
  def report(interface: Interface): Item = {
    import scala.text.Document
    import scala.text.Document._
    //collect the objects


    val idsForCover = interface.vertices.iterator.zipWithIndex.map{ case (o, idx) => (o, "cover_"+idx) }.toMap
    val idsForTransitions = interface.edges.iterator.zipWithIndex.map{ case (t, idx) => (t._2, "t_"+idx) }.toMap

    def gToGv(g: G, id: String, kind: String = "digraph", misc: Document = empty, roles: Map[G#V, String] = Map.empty): (Document, Map[G#V, String]) = {
      def idsForObj(obj: G#V) = {
        val (tpe, ptsTo, unary, binary) = obj.state
        val flatBinary = for ( (p, fb) <- binary; (f,b) <- fb) yield (p,f,b)
        val name = 
          if (roles.contains(obj)) roles(obj) + ": " + tpe
          else tpe
        Misc.quote(
          "{ " + name + " | " +
          unary.map{ case (n,b) => if (b) n else "not " + n }.mkString(" | ") +
          flatBinary.mkString(" | ") +
          "}"
        )
      }

      g.toGraphvizWithNesting(
        id, kind, misc, id,
        (node => List("label" -> idsForObj(node), "shape" -> "record")),
        (edge => Nil)
      )
    }

    def mkTitle(method: String, roles: Map[G#V, String]): String = {
        val objByRole = roles.map[(String, G#V), Map[String, G#V]]{ case (a, b) => (b, a) }
        val calleeName = objByRole.get("callee") match {
          case Some(cl) => objToString(cl.state)
          case None => "???"
        }
        val args = for (i <- 0 until roles.size -1) yield {
          objByRole.get("arg" + i) match {
            case Some(cl) => objToString(cl.state)
            case None => "???"
          }
        }
        calleeName + "." + method + args.mkString("(", ", ", ")")
    }

    def multiplicityToEdgeProp(m: Multiplicity) = m match {
      case One => "color=\"#00FF00\""
      case May => "color=\"#00FF00\",style=\"dashed\""
      case Part => "color=\"#0000FF\""
      case Rest => "color=\"#0000FF\""
    }

    def completeRoleWithScope(g: G, roles: Map[G#V, String]): Map[G#V, String] = {
      val scope = g.vertices.filter(_.depth == 0) -- roles.keys
      (roles /: scope.zipWithIndex)( (acc, s) => acc + (s._1 -> ("s" + s._2)))
    }

    def keepRelevantEdges(changes: Changes[G#V]): Changes[G#V] = {
      changes.filter{ case (k, v) => v.size != 1 || k.depth > 0 }
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
    val trsGraphs = interface.edges.map{ case (coverFrom , el @ (from, roles, method, changes, news, to), coverTo) =>
        val id = idsForTransitions(el)
        val title = mkTitle(method, roles)
        val rolesWithScope = completeRoleWithScope(from, roles)
        val (fromGv, fromNodesToId) = gToGv(from, "cluster_" + id + "_src", "subgraph", text("label = \"LHS("+idsForCover(coverFrom)+")\";"), rolesWithScope)
        val newsRole =  news.zipWithIndex.map{ case (n,i) => (n, "new"+i) }
        val rolesAfter = rolesWithScope.flatMap[(G#V, String),Map[G#V, String]]{ case (n, r) => changes.get(n).map(_.head._2 -> r) } ++ newsRole //TODO some assertion
        val (toGv, toNodesToId) = gToGv(to, "cluster_" + id + "_to", "subgraph", text("label = \"RHS("+idsForCover(coverTo)+")\";"), rolesAfter)
        val changesEdges = keepRelevantEdges(changes).iterator.flatMap{ case (a, bs) => bs.map{ case (m, b) =>
            text( fromNodesToId(a) + " -> " + toNodesToId(b) + " ["+ multiplicityToEdgeProp(m) +"];")
          }
        }
        val graphs = fromGv :/: toGv
        val body = (graphs /: changesEdges)(_ :/: _)
        val gv = "digraph " :: id :: " {" :/: nest(4, body) :/: text("}")
        Logger("InterfaceExtraction", LogDebug, title + ": " + Misc.docToString(gv))
        (id, title, gv)
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
      val withLower = restricted.vertices.map(v => (v, v.setDepth(math.max(0, v.depth - height))) )
      val morphing = withLower.toMap[P#V,P#V]
      (morphing(node), restricted morph morphing)
    } else {
      (node, restricted)
    }
  }

  protected def inDPV(d1: DPV, d2: DPV): Boolean = {
    //check whether there is a morphism between d1 and d2 (compatible with the main obj)
    d1._2.morphisms(d2._2, Map(d1._1 -> d2._1))(proc.stateOrdering).hasNext
  }

  protected def sameDPV(d1: DPV, d2: DPV): Boolean = {
    inDPV(d1, d2) && inDPV(d2, d1)
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
    val candidate = eqClassesInGraph.find( dpv => inDPV(extracted, dpv) )
    Logger.assert(
        candidate.isDefined,
        "InterfaceExtraction",
        "findClassOf: no candidate found for " + obj + "\n" + conf + extracted._1 + "\n" + extracted._2
        + "in\n" + eqClassesMap.keys.mkString("\n")
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

  protected def backwardTracking(curr: (Changes[P#V], List[P#V]), mapping: Map[P#V, Seq[P#V]]) = {
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

  /* Adapting the tracking to get the unfolded version
     first -> unfolded in the base of the tracking
     last -> stops before the folding
  */
  protected def trackAux(curr: (Changes[P#V], List[P#V]), edge: TGEdges[P], first: Boolean = false, last: Boolean = false): (Changes[P#V], List[P#V]) = edge match {
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
        else if (first) initialTracking(witness.unfolded)
        else backwardTracking( curr, witness.reversedUnfolding)
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
        if (witness.isFoldingTrivial || last) curr4
        else simpleTracking(curr4, witness.folding)
      curr5
    case Covering(mapping) =>
      Logger.assert(!(first || last), "InterfaceExtraction", "track: Covering edge for first or last")
      //println("following covering")
      simpleTracking(curr, mapping)
  }
  
  protected def track(curr: (Changes[P#V], List[P#V]), edge: TGEdges[P]) =
    trackAux(curr, edge, false, false)

  protected def trackFirst(curr: (Changes[P#V], List[P#V]), edge: TGEdges[P]) =
    trackAux(curr, edge, true, false)
  
  protected def trackLast(curr: (Changes[P#V], List[P#V]), edge: TGEdges[P]) =
    trackAux(curr, edge, false, true)
  
  protected def trackFirstLast(curr: (Changes[P#V], List[P#V]), edge: TGEdges[P]) =
    trackAux(curr, edge, true, true)

  /** identify the objects in a DP and make a map to self */
  protected def initialTracking(from: DP) = {
    val objsNode: Set[P#V] = from.vertices.filter(isObj)
    val iter: Iterator[(P#V, Seq[(Multiplicity, P#V)])] = objsNode.iterator.map(n => (n, Seq( (if (n.depth == 0) One else Rest) -> n)))
    val objsMap: Changes[P#V] = Map[P#V, Seq[(Multiplicity, P#V)]]() ++ iter
    (objsMap, List[P#V]())
  }

  protected def withType(nodes: Iterable[P#V], tpe: ObjType, role: String): Option[P#V] = {
    val candidates = nodes.filter(n => typeOf(n) == tpe)
    if (candidates.isEmpty) {
      Logger("InterfaceExtraction", LogWarning, "pathToMethodCall: no candidates for " + role)
      None
    } else {
      if (candidates.size > 1) {
        Logger( "InterfaceExtraction",
                LogWarning,
                "pathToMethodCall: more than one candidate for " + role + ": " + candidates.mkString(", ")
              )
      }
      Some(candidates.head)
    }
  }

  protected def nodeWithID(witness: TransitionWitness[P], conf: DP, id: String): Option[P#V] = {
    witness.lhsIDs.find{ case (a,b) => b == id } match {
      case Some((n,_)) =>
         Logger.assert(conf contains n, "InterfaceExtraction", id + " in lhsIDs but not conf.")
         Some(n)
      case None =>
        Logger("InterfaceExtraction", LogWarning, "pathToMethodCall: no candidates for " + id)
        None
    }
  }

  // parse the comment from the transition to get the method name and the type/id of the callee
  protected def parseTransition(edge: TGEdges[P]): (Map[P#V, String], String, Option[ObjType]) = edge match {
    case Transition(witness) =>
      Logger("InterfaceExtraction", LogInfo, "making edge for: " + witness.transition.id)
      parseTransitionName(witness.transition.id) match {
        case Some((tpe, call, args, created)) =>
          //println("looking for candidate of type " + tpe + " in " + witness.modifiedPre.map(typeOf).mkString(", "))
          val concreteNodes = witness.modifiedUnfolded.filter(n => n.depth == 0)
          val callee: Option[P#V] = nodeWithID(witness, witness.unfolded, "callee")
          val indexed: Iterable[(ObjType, Int)] = args.zipWithIndex
          val initRole: Map[P#V, String] =
            if(callee.isDefined) Map[P#V, String](callee.get -> "callee")
            else Map.empty[P#V, String]
          val roles: Map[P#V, String] = (initRole /: indexed)( (acc, a) => {
            val role = "arg" + a._2
            val candidate: Option[P#V] = nodeWithID(witness, witness.unfolded, role)
            if (candidate.isDefined) acc + (candidate.get -> role)
            else acc
          })
          (roles, call, created)
        case None =>
          Logger("InterfaceExtraction", LogWarning, "pathToMethodCall: cannot parse \""+witness.transition.id+"\"")
          (Map.empty[P#V, String], "---", None)
      }
    case _ => Logger.logAndThrow("InterfaceExtraction", LogError, "pathToMethodCall: expected Transition")
  }

  protected def removePreds(conf: DP): (G, Map[P#V, G#V]) = {
    val (objNode, predNodes) = conf.vertices.partition(isObj)
    val nodeTObj = objNode.iterator.map( v => (v, Thread(eqClassToObj(findClassOf(conf,v)), v.depth)) ).toMap[P#V, G#V]
    val objOnly = conf -- predNodes
    (objOnly.morphFull[IGT](nodeTObj, x => x.toString, x => (x.state, x.depth)), nodeTObj)
  }
  
  protected def composeTracking( t1: (Changes[P#V], List[P#V]),
                                 t2: (Changes[P#V], List[P#V])
                               ): (Changes[P#V], List[P#V])= {
    val (t1Changes, t1News) = t1
    val (t2Changes, t2News) = t2
    val resChanges = t1Changes.map[(P#V, Iterable[(Multiplicity, P#V)]), Changes[P#V]]{ case (a, bs) =>
        (a, bs.flatMap{ case (m, b) =>
          t2Changes(b).map{ case (m2, b2) => (composeMultiplicities(m, m2), b2) }
      })
    }
    val resNews = t1News.flatMap( n => t2Changes(n).map(_._2) )
    (resChanges, resNews)
  }
  /* a trace should start in a non-transient cover location,
   *  end in a non-transient cover location, and includes the transient loops. */
  protected def traceToMethodCall(trace: Trace[DP, TGEdges[P]]): (DP, MethodCall, DP) = {
    //get the differents parts of the trace:
    // the first transition -> track after the unfolding
    val ((s1, transition1), tail1) = trace.step
    val ((s2, cover1), tail2) = tail1.step
    // the loops -> accelerate and track
    val (loops, tail3) = tail2.splitAfter(tail2.length - 2)
    // sanity checks
    Logger.assert(!isTransient(s1), "InterfaceExtraction", "traceToMethodCall: transient start")
    Logger.assert(loops.states.dropRight(1).forall(isTransient), "InterfaceExtraction", "non-transient middle")
    //
    //parse the comment from the transition to get the method name and the type/id of the callee
    val (roles, method, createdTpe) = parseTransition(transition1)
    //follows ....
    val initTracking = initialTracking(s1)
    val (goesTo, news, last) = if (loops.isEmpty) {
      val last = transition1 match {
        case Transition(witness) => witness.unfoldedAfterPost
        case _ => Logger.logAndThrow("InterfaceExtraction", LogError, "expected Transition")
      }
      val (a,b) = trackFirstLast(initTracking, transition1)
      (a,b,last)
    } else {
      // the last transition -> stops tracking before the unfolding
      val ((endOfLoop, lastTransition), end) = tail3.step
      val last = lastTransition match {
        case Transition(witness) => witness.unfoldedAfterPost
        case _ => Logger.logAndThrow("InterfaceExtraction", LogError, "expected Transition")
      }
      //the prefix
      val firstChange = track(trackFirst(initTracking, transition1), cover1)
      //the loop
      val loopTracking = initialTracking(loops.start)
      val (loopChanges, loopNews) = (loopTracking /: loops.labels)(track)
      Logger.assert(loopNews.isEmpty, "InterfaceExtraction", "TODO new object and acceleration")
      val accelerated = loopAcceleration(loopChanges) //, (x: EqClass, y: EqClass) => x.obj == y.obj)
      //the suffix
      val lastTracking = initialTracking(endOfLoop)
      val lastChange = trackLast(lastTracking, lastTransition)
      //compose ...
      val (a, b) = List(firstChange, (accelerated, loopNews), lastChange) reduceLeft composeTracking
      (a, b, last)
    }
    Logger.assert(!isTransient(last), "InterfaceExtraction", "traceToMethodCall: transient stop")
    val (src, srcMap) = transition1 match {
      case Transition(witness) => removePreds(witness.unfolded)
      case _ => Logger.logAndThrow("InterfaceExtraction", LogError, "expected Transition")
    }
    val (dst, dstMap) = removePreds(last)
    val becomesObj = simplify(goesTo.map{ case (k,vs) =>
        (srcMap(k), vs map { case (m, cl) =>
            (m, dstMap(cl)) } ) })
    val newsObj = news map dstMap 
    val roles2 = roles.map[(G#V, String), Map[G#V, String]]{ case (node, role) => (srcMap(node), role) }
    val call = (src, roles2, method, becomesObj, newsObj, dst)
    (trace.start, call, trace.stop)
  }

  protected def makeNormalTraces: Iterable[Trace[DP, TGEdges[P]]] = {
    //normal traces
    val paths = tg.simplePaths
    Logger.assert(paths.forall(p => cover.contains(p.start) && cover.contains(p.stop)),
                  "InterfaceExtraction",
                  "TODO makeTraces: a more complex way of spliting the paths ...")
    val paths2 = paths.view.flatMap(p => p.split(loc => cover.basis.contains(loc)))
    val paths3 = paths2.filter(p => !isTransient(p.start) && !isTransient(p.stop) )
    paths3.force
  }

  protected def makeTransientTraces: Iterable[Trace[DP, TGEdges[P]]] = {
    // tg: EdgeLabeledDiGraph[TG[P]]
    val revTG = tg.reverse
    val transientStates = cover.basis.seq.filter(isTransient)
    
    //includes the self loops
    def mkTransientPath(t: DP): Iterable[Trace[DP, TGEdges[P]]] = {
      //needs to do two steps because of the way the tg graph is ...
      def twoStepsTo( from: DP,
                      graph: EdgeLabeledDiGraph[TG[P]],
                      pred: DP => Boolean
                    ): Iterable[(TGEdges[P], DP, TGEdges[P], DP)] = {
        for( (label1, dest1) <- graph.outEdges(from);
             s1 <- dest1;
             (label2, dest2) <- graph.outEdges(s1);
             s2 <- dest2 if pred(s2))
        yield (label1, s1, label2, s2)
      }
      def twoStepsToConcrete(from: DP,  graph: EdgeLabeledDiGraph[TG[P]]) = 
        twoStepsTo(from, graph, x => !isTransient(x))
      def twoStepsToSelf(from: DP,  graph: EdgeLabeledDiGraph[TG[P]]) = 
        twoStepsTo(from, graph, x => x == from)

      val prefixes = twoStepsToConcrete(t, revTG)
      val loops = twoStepsToSelf(t, tg)
      val suffixes = twoStepsToConcrete(t, tg)

      Logger("InterfaceExtraction", LogDebug, "#prefixes: " + prefixes.size)
      Logger("InterfaceExtraction", LogDebug, "#loops: " + loops.size)
      Logger("InterfaceExtraction", LogDebug, "#suffixes: " + suffixes.size)

      for ( (c2, s2, c1, s1) <- prefixes;
            (c3, s3, c4, s4) <- loops;
            (c5, s5, c6, s6) <- suffixes )
          yield Trace(s1, (c1, s2), (c2, t), (c3, s3), (c4, t), (c5, s5), (c6, s6))
    }
    val traces = transientStates.iterator.flatMap( mkTransientPath ).toIterable
    traces
  }

  protected def makeTraces = {
    val traces = makeNormalTraces ++ makeTransientTraces
    Logger("InterfaceExtraction", LogInfo, "transitions are:\n" + traces.map(_.labels.mkString("; ")).mkString("\n"))
    Logger.assert(
      {
        val trs = (0 /: traces)( (acc, t) => acc + t.length)
        trs >= tg.edges.size
      },
      "InterfaceExtraction",
      "makeTraces is not covering the whole graph"
    )
    traces
  }

  def pruneCall(call: MethodCall): MethodCall = {
    //TODO connected component rather than changed.
    val (src, roles, method, changes, news, dst) = call
    val lhsSeeds = roles.keySet
    val toKeep = (Set.empty[G#V] /: src.CC)( (acc, cc) => if (cc exists lhsSeeds) acc ++ cc else acc )
    val src2 = src.filterNodes(toKeep)
    val changes2 = changes.filterKeys(toKeep)
    val changesRange = changes2.values.flatMap(_.map(_._2)).toSet
    val newsSet = news.toSet
    val dst2 = dst.filterNodes(n => newsSet(n) || changesRange(n) )
    (src2, roles, method, changes2, news, dst2)

    /*
    val changes2 = changes.filterNot{ case (a,bs) => 
      if (!roles.contains(a) && bs.size == 1) {
        val (m, b) = bs.head
        (m == Rest && b.state == a.state)
      } else false
    }
    val src2 = src.filterNodes(n => roles.contains(n) || changes2.keySet(n))
    val changesRange = changes2.values.flatMap(_.map(_._2)).toSet
    val newsSet = news.toSet
    val dst2 = dst.filterNodes(n => newsSet(n) || changesRange(n) )
    (src2, roles, method, changes2, news, dst2)
    */
  }
  
  def interface: Interface = {
    Logger("InterfaceExtraction", LogNotice, "Extracting interface ...")
    Logger( "InterfaceExtraction", LogDebug, Misc.docToString(
        TransitionsGraphFromCover.structureToGraphviz(cover, tg) ) )

    val dict = cover.basis.seq.iterator.map( c => (c, removePreds(c)._1) ).toMap
    val edges: Iterable[(G, MethodCall, G)] = makeTraces.map( t => {
      val (a,b,c) = traceToMethodCall(t)
      (dict(a), pruneCall(b), dict(c))
    })
    val nodes = cover.basis.seq.filter(x => !isTransient(x)).map(dict)
    EdgeLabeledDiGraph[IGT2](edges).addVertices(nodes)

  }

}
