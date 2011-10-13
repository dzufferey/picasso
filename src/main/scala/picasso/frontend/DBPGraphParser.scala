package picasso.frontend

import picasso.model.dbp._
import picasso.math._
import picasso.utils._
import picasso.frontend.DBPGraphs._
import scala.util.parsing.combinator._
import scala.util.parsing.combinator.lexical._
import scala.util.parsing.combinator.token._
import scala.util.parsing.combinator.syntactical._

object DBPGraphParser extends StandardTokenParsers {
  lexical.delimiters += ("[", "]", ",", "(", ")", "==>", "<==", "->")
  lexical.reserved += ("transition", "init", "target", "node", "pre", "post", "_")

  private def nodeInGraph(node: Node, graph: DepthBoundedConf[DBCGraph]): DBCGraph#V = {
    val n = graph.vertices.find( n => n.state._1 == node._1 ).getOrElse(Thread(node))
    assert(n.state._2 == node._2)
    n
  }
  private def nodeInGraph(node: NodeId, graph: DepthBoundedConf[DBCGraph]): DBCGraph#V = {
    graph.vertices.find( n => n.state._1 == node ).get
  }

  def node: Parser[DBCGraph#State] = 
    ( ("(" ~> ident <~ ",") <~ "_" <~ ")"    ^^ { case id => new Node(id, None) }
    | ("(" ~> ident <~ ",") ~ ident <~ ")"   ^^ { case id ~ label => new Node(id, Some(label)) }
    )

  def edge: Parser[(DBCGraph#State, DBCGraph#EL, DBCGraph#State)] =
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
    ("transition" ~> stringLit) ~ ("pre" ~> graph) ~ ("post" ~> graph) ~ ("==>" ~> mapping) ~ ("<==" ~> mapping) ^^ {
      case id ~ lhs ~ rhs ~ forward ~ backward =>
        val hr = forward.map{ case (k,v) => (nodeInGraph(k, lhs), nodeInGraph(v, rhs))}
        val hk = backward.map{ case (k,v) => (nodeInGraph(k, rhs), nodeInGraph(v, lhs))}
        DepthBoundedTransition[DBCGraph](id, lhs, rhs, hr, hk, None)
    }

  def system: Parser[(DepthBoundedConf[DBCGraph], List[DepthBoundedTransition[DBCGraph]], Option[DepthBoundedConf[DBCGraph]])] =
    ("init" ~> graph) ~ rep(transition) ~ opt("target" ~> graph) ^^ { case init ~ trs ~ target => (init, trs, target) }
    
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

  //TODO run the analysis ?

}

