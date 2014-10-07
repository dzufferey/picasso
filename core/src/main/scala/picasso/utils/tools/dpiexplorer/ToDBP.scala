package picasso.utils.tool.dpiexplorer

import picasso.frontend.dbpGraph.DBPGraphs._
import picasso.model.dbp._
import picasso.math._
import scala.util._
import picasso.utils._

object ToDBP {

  protected val safeToken = Thread(new Node("_s", Some("safe")), 0)
  protected def errorToken(err: String) = Thread(new Node("_e", Some("error: " + err)), 0)
  protected def transientToken(t: String) = Thread(new Node("_t", Some("transient: " + t)), 0)

  protected def mkPredNode(src: Int, name: String, value: Boolean, depth: Int) = {
    val label = if (value) name else "not_" + name
    Thread(new Node(name + "_" + src, Some(label)), depth)
  }

  protected def graph(g: GraphDescr): DepthBoundedConf[DBCGraph] = {
    val nDecr = g.nodes.map(n => Pair(n.id, n)).toMap
    val nodes = nDecr.map{ case (id,n) => Pair(id, Thread(new Node(n.id.toString, Some(n.clazz)), n.depth)) }

    val edges = g.edges.map(e => (nodes(e.src), nodes(e.dst)))

    def getSucc(id: Int): List[NodeDescr] =
      g.edges.flatMap{ case EdgeDescr(s, d) => if (s == id) Some(nDecr(d)) else None }

    val preds: List[Either[(Int, String, Option[Boolean]), (Int, String, Option[Boolean], Int)]] =
      g.nodes.flatMap( n => {
        //get successors
        val succ = getSucc(n.id)
        n.predicates.map( p => {
          succ.find(s => s.binaryPredicates.contains(p._1)) match {
            case Some(s) => Right((n.id,p._1,p._2,s.id)) //binary
            case None => Left((n.id,p._1,p._2)) //unary
          }
        })
      })
    
    val binPredAnchors =
      for( n <- g.nodes;
           p <- n.binaryPredicates;
           b <- List(true, false) )
      yield (n.id, p, b, mkPredNode(n.id, p, b, n.depth))

    def findAnchor(id: Int, name: String, value: Boolean) = {
      binPredAnchors.find(a => a._1 == id && a._2 == name && a._3 == value) match {
        case Some(a) => a._4
        case None => Logger.logAndThrow("dpiexplorer.ToDBP", LogError, "could not find anchor")
      }
    }

    val g0 = DepthBoundedConf.empty[DBCGraph]
    val g1 = nodes.foldLeft(g0)((acc, kv) => acc + kv._2)
    val g2 = edges.foldLeft(g1)((acc, sd) => acc + (sd._1, "", sd._2))
    val g3 = binPredAnchors.foldLeft(g2)( (acc, in) => acc + (nodes(in._1), "", in._4))
    val g4 = preds.foldLeft(g3)( (acc, pred) => pred match {
        case Left((id,p,Some(v))) => acc + (nodes(id), "", mkPredNode(id, p, v, nodes(id).depth))
        case Right((src,p,Some(v),dst)) => acc + (nodes(src), "", findAnchor(dst, p, v))
        case _ => acc
      })

    //TODO the "safe" token ?
    g4
  }

  private def nodeInGraph(node: NodeId, graph: DepthBoundedConf[DBCGraph]): DBCGraph#V = {
    graph.vertices.find( n => n.state._1 == node ) match {
      case Some(n) => n
      case None => Logger.logAndThrow("ToDBP", LogError, "cannot find node with id " + node)
    }
  }

  //transient loops ??
  
  //error: Option[String],
  //roleMapping: List[MappingDescr],
  //objectMapping: List[MappingDescr]
  //unknown predicate value requires case split

  protected def forwardMapping(src: DepthBoundedConf[DBCGraph],
                               edges: List[MappingDescr],
                               dst: DepthBoundedConf[DBCGraph])
                            : Map[DBCGraph#V,DBCGraph#V] =
  {
    edges.foldLeft(Map(): Map[DBCGraph#V,DBCGraph#V])((acc, m) => {
      Logger.assert(m.dsts.length == 1, "ToDBP", "mapping with more than one destination")
      val d = m.dsts.head._1
      acc + (nodeInGraph(m.src.toString, src) -> nodeInGraph(d.toString, dst))
    })
  }

  protected def normalTransition(descr: RuleDescr): List[DepthBoundedTransition[DBCGraph]] = {
    val id = "(" + descr.id + ") "+ descr.name + descr.returns.map(b => ": " + b).getOrElse("")
    val gSrc = graph(descr.src) + safeToken
    //TODO transient loops ? cannot get the forward mapping with mutliple dst node
    //loop:
    //  first transition do the deterministic mapping and introduce the transient token (connected to the modified object) instead of the safe one
    //  the loop randomly takes some objets to their changed predicate
    //  exit loop transition: remove transient token and put back the safe one
    val gDst = graph(descr.dst)
    //add safe token
    sys.error("TODO")
  }

  protected def errorTransition(descr: RuleDescr): DepthBoundedTransition[DBCGraph] = {
    val id = "(" + descr.id + ") "+ descr.name + ": " + descr.error.get
    val gSrc = graph(descr.src) + safeToken
    val gDst = graph(descr.dst) + errorToken(descr.error.get)
    val map1 = forwardMapping(gSrc, descr.roleMapping, gDst)
    //val map2 = forwardMapping(gSrc, descr.objectMapping, gDst)
    val lhsId = gSrc.vertices.iterator.map[(DBCGraph#V, String)]( n => (n, n.state._1) ).toMap
    DepthBoundedTransition[DBCGraph](id, gSrc, gDst, map1, Map(), None, lhsId)
  }
  
  protected def unfoldAndClean(descr: RuleDescr, trs: DepthBoundedTransition[DBCGraph])
                                : List[DepthBoundedTransition[DBCGraph]] = {
    //cannot have nesting on the LHS
    //roles requires unfolding
    //many -> many,many requires loops
    //many -> one,many requires unfolding
    //remove the frame
    sys.error("TODO")
  }
  
  protected def unfoldRoles(descr: RuleDescr): List[RuleDescr] = {
    //cannot have nesting on the LHS
    //roles requires unfolding
    sys.error("TODO")
  }

  protected def removeFrame(descr: RuleDescr): RuleDescr = {
    sys.error("TODO")
  }


  protected def transition(descr: RuleDescr): List[DepthBoundedTransition[DBCGraph]] = {
    val trs =
        if (descr.error.isDefined) List(errorTransition(descr))
        else normalTransition(descr)
    trs.flatMap( x => unfoldAndClean(descr, x) )
  }

  protected def makeInitialState(proc: DepthBoundedProcess[DBCGraph]): DepthBoundedConf[DBCGraph] = {
    //collect of the graphs, check the connected cmpt
    //look for the biggest graph such that transition can reach everything
    sys.error("TODO")
  }

  def apply(input: SystemDescr): Option[(DepthBoundedProcess[DBCGraph],
                                         DepthBoundedConf[DBCGraph],
                                         Option[DepthBoundedConf[DBCGraph]])] =
  {
    sys.error("TODO")
  }

}
