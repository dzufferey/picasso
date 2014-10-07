package picasso.utils.tool.dpiexplorer

sealed abstract class Descr
case class NodeDescr(id: Int, clazz: String, depth: Int,
                     predicates: List[(String,Option[Boolean])],
                     binaryPredicates: List[String]) extends Descr
case class EdgeDescr(src: Int, dst: Int) extends Descr
case class MappingDescr(role: String, src: Int, dsts: List[(Int,Boolean)]) extends Descr //(Int,Boolean) -> (ID, Many)
case class GraphDescr(nodes: List[NodeDescr], edges: List[EdgeDescr]) extends Descr
case class RuleDescr(name: String, error: Option[String], id: Int, returns: Option[Boolean],
                     src: GraphDescr, dst: GraphDescr,
                     roleMapping: List[MappingDescr], objectMapping: List[MappingDescr]) extends Descr
case class SystemDescr(name: String, rules: List[RuleDescr]) extends Descr
