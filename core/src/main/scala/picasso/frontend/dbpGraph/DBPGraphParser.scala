package picasso.frontend.dbpGraph

import DBPGraphs._
import picasso.model.dbp._
import picasso.math._
import picasso.utils._
import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.combinator.syntactical._

object DBPGraphParser extends StandardTokenParsers {
  lexical.delimiters += ("[", "]", ",", "(", ")", "==>", "<==", "->", "*")
  lexical.reserved += ("transition", "init", "target", "node", "pre", "post", "no", "_")

  private def nodeInGraph(node: DBCGraph#V, graph: DepthBoundedConf[DBCGraph]): DBCGraph#V = {
    val n = graph.vertices.find( n => n.state._1 == node.state._1 ).getOrElse(node)
    assert(n.state._2 == node.state._2 && n.depth == node.depth, n + " != " + node)
    n
  }
  private def nodeInGraph(node: NodeId, graph: DepthBoundedConf[DBCGraph]): DBCGraph#V = {
    graph.vertices.find( n => n.state._1 == node ) match {
      case Some(n) => n
      case None => Logger.logAndThrow("dbpGraph", LogError, "cannot find node with id " + node)
    }
  }

  def node1: Parser[Node] = 
    ( ("(" ~> ident <~ ",") <~ "_" <~ ")"    ^^ { case id => new Node(id, None) }
    | ("(" ~> ident <~ ",") ~ ident <~ ")"   ^^ { case id ~ label => new Node(id, Some(label)) }
    )

  def node: Parser[DBCGraph#V] = 
    ( node1 ~ rep("*")                        ^^ { case node ~ depth => Thread(node, depth.length) }
    )

  def edge: Parser[(DBCGraph#V, DBCGraph#EL, DBCGraph#V)] =
    ( node ~ ("->" ~> node) ~ opt("[" ~> (ident | numericLit) <~ "]")  ^^ { case n1 ~ n2 ~ label => (n1, label getOrElse "", n2) }
    )

  def graph: Parser[DepthBoundedConf[DBCGraph]] =
    ( "node" ~> node ~ graph    ^^ { case n ~ g => g + nodeInGraph(n, g) }
    | edge ~ graph              ^^ { case (n1,l,n2) ~ g => g + (nodeInGraph(n1,g), l, nodeInGraph(n2,g)) }
    | success(DepthBoundedConf.empty[DBCGraph])
    )

  def mapping : Parser[Map[NodeId, NodeId]] =
    rep(ident ~ ("->" ~> ident))  ^^ ( lst => (Map[NodeId, NodeId]() /: lst)( (acc, p) => p match { case id1 ~ id2 => acc + (id1 -> id2) } ) )

  def transition : Parser[DepthBoundedTransition[DBCGraph]] =
    ("transition" ~> stringLit) ~
    ("pre" ~> graph) ~
    ("post" ~> graph) ~
    ("==>" ~> mapping) ~
    ("<==" ~> mapping) ~
    opt(("no" ~> graph) ~ opt("==>" ~> mapping)) ^^ {
      case id ~ lhs ~ rhs ~ forward ~ backward ~ inhibitory =>
        val hr = forward.map{ case (k,v) => (nodeInGraph(k, lhs), nodeInGraph(v, rhs))}
        val hk = backward.map{ case (k,v) => (nodeInGraph(k, rhs), nodeInGraph(v, lhs))}
        val inhibitory2 = for ( (inh ~  map) <- inhibitory ) yield {
          val map2 = map.getOrElse(Map())
          val map3 = map2.map{ case (k,v) => (nodeInGraph(k, lhs), nodeInGraph(v, inh))}
          (inh, map3)
        }
        DepthBoundedTransition[DBCGraph](id, lhs, rhs, hr, hk, inhibitory2)
    }

  def system: Parser[(DepthBoundedConf[DBCGraph], List[DepthBoundedTransition[DBCGraph]], Option[DepthBoundedConf[DBCGraph]])] =
    ("init" ~> graph) ~ rep(transition) ~ opt("target" ~> graph) ^^ { case init ~ trs ~ target => (init, trs, target) }
    
  def parseGraph(str: String): Option[DepthBoundedConf[DBCGraph]] = {
    val tokens = new lexical.Scanner(str)
    val result = phrase(graph)(tokens)
    if (result.successful) {
      Some(result.get)
    } else {
      Logger("DBPGraphParser", LogError, "parsing error (graph): " + result.toString)
      None
    }
  }

  def apply(str: String): Option[(DepthBoundedConf[DBCGraph], List[DepthBoundedTransition[DBCGraph]], Option[DepthBoundedConf[DBCGraph]])] = {
    val tokens = new lexical.Scanner(str)
    val result = phrase(system)(tokens)
    if (result.successful) {
      Some(result.get)
    } else {
      Logger("DBPGraphParser", LogError, "parsing error: " + result.toString)
      None
    }
  }

}

