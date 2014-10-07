package picasso.utils.tool.dpiexplorer

import picasso.utils._
import scala.util.parsing.json._

//parsing rules from Shahram's tool http://www.mpi-sws.org/~shahram/DPIExplorer/

object Parser {

  protected def parsePred(json: Any): (String,Option[Boolean]) = json match {
    case JSONObject(map) =>
      val name = map("NAME").toString
      val value = map("VALUE") match {
        case "TRUE" | "true" | true => Some(true)
        case "FALSE" | "false" | false => Some(false)
        case "*" => None
        case _ =>
          Logger.logAndThrow("dpiexplorer.Parser.parsePred", LogError, "unknown predicate value")
      }
      (name, value)
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parsePred", LogError, "expected JSON object")
  }
  
  protected def parseBPred(json: Any): String = json match {
    case JSONObject(map) => map("NAME").toString
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parsePred", LogError, "expected JSON object")
  }

  protected def parseNode(json: Any): NodeDescr = json match {
    case JSONObject(map) =>
      val id = map("ID").toString.toInt
      val clazz = map("CLASS").toString
      val depth = map("NESTING").toString.toInt
      val predicates = map("PREDICATES") match {
          case JSONArray(lst) => lst.map(parsePred)
          case _ =>
            Logger.logAndThrow("dpiexplorer.Parser.parseNode", LogError, "expected JSON array")
        }
     val binPreds = map("BINARYPREDS") match {
          case JSONArray(lst) => lst.map(parseBPred)
          case _ =>
            Logger.logAndThrow("dpiexplorer.Parser.parseNode", LogError, "expected JSON array")
        }
        NodeDescr(id, clazz, depth, predicates, binPreds)
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parseNode", LogError, "expected JSON object")
  }

  protected def parseEdge(json: Any): EdgeDescr = json match {
    case JSONObject(map) =>
      val src = map("SOURCENODE").toString.toInt
      val dst = map("DESTNODE").toString.toInt
      EdgeDescr(src, dst)
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parseEdge", LogError, "expected JSON object")
  }
  
  protected def parseDest(json: Any): (Int, Boolean) = json match {
    case JSONObject(map) =>
      val dst = map("DESTID").toString.toInt
      val mlt = map("MULT") match {
        case "ONE" => false
        case "MANY" => true
      }
      (dst, mlt)
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parseDest", LogError, "expected JSON object")
  }
  
  protected def parseGraph(json: Any): GraphDescr = json match {
    case JSONObject(map) =>
      val nodes = map("NODES") match {
        case JSONArray(lst) => lst.map(parseNode)
        case _ =>
          Logger.logAndThrow("dpiexplorer.Parser.parseGraph", LogError, "expected JSON array")
      }
      val edges = map("EDGES") match {
        case JSONArray(lst) => lst.map(parseEdge)
        case _ =>
          Logger.logAndThrow("dpiexplorer.Parser.parseGraph", LogError, "expected JSON array")
      }
      GraphDescr(nodes, edges)
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parseGraph", LogError, "expected JSON object")
  }

  protected def parseMapping(json: Any): MappingDescr = json match {
    case JSONObject(map) =>
      val role = map("ROLE").toString
      val src = map("SOURCEID").toString.toInt
      val dsts = map("DESTS") match {
        case JSONArray(lst) => lst.map(parseDest)
        case _ =>
          Logger.logAndThrow("dpiexplorer.Parser.parseMapping", LogError, "expected JSON array")
      }
      MappingDescr(role, src, dsts)
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parseMapping", LogError, "expected JSON object")
  }

  protected def parseRule(json: Any): RuleDescr = json match {
    case JSONObject(map) =>
      val name = map("NAME")
      val err = map("ERROR") match {
        case x: String => if (x == "") None else Some(x) 
        case _ => 
          Logger.logAndThrow("dpiexplorer.Parser.parseRule", LogError, "expected JSON string")
      }
      val nbr = map("NUMBER").toString.toInt
      val ret = map("RETURNS") match {
        case "TRUE" | "true" | true => Some(true)
        case "FALSE" | "false" | false => Some(false)
        case "" => None
        case _ => 
          Logger.logAndThrow("dpiexplorer.Parser.parseRule", LogError, "expected JSON bool")
      }
      val src = parseGraph(map("SOURCEGRAPH"))
      val dst = parseGraph(map("DESTGRAPH"))
      val roles = map("ROLEMAPPINGS") match {
        case JSONArray(lst) => lst.map(parseMapping)
        case _ =>
          Logger.logAndThrow("dpiexplorer.Parser.parseRule", LogError, "expected JSON array")
      }
      val objs = map("OBJECTMAPPINGS") match {
        case JSONArray(lst) => lst.map(parseMapping)
        case _ =>
          Logger.logAndThrow("dpiexplorer.Parser.parseRule", LogError, "expected JSON array")
      }
      ???
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parseRule", LogError, "expected JSON object")
  }

  protected def parseIntput(json: JSONType): SystemDescr = json match {
    case JSONObject(map) =>
      val name = map("DPINAME").toString
      val rules = map("RULES") match {
        case JSONArray(lst) => lst.map(parseRule)
        case _ =>
          Logger.logAndThrow("dpiexplorer.Parser.parseIntput", LogError, "expected JSON array")
      }
      SystemDescr(name, rules)
    case _ =>
      Logger.logAndThrow("dpiexplorer.Parser.parseIntput", LogError, "expected JSON object")
  }

  def apply(input: String): Option[SystemDescr] = {
    JSON.parseRaw(input) match {
      case Some(json) =>
        try Some(parseIntput(json))
        catch {
          case _: Exception =>
            Logger("dpiexplorer.Parser", LogError, "failed to build the transition from JSON object")
            None
        }
      case None =>
        Logger("dpiexplorer.Parser", LogError, "parsing error")
        None
    }
  }

}
