package picasso.frontend.compilerPlugin.domains

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin._
import picasso.ast.{Ident => PIdent, Process => PProcess, Block => PBlock, Value => PValue, _}
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, Wildcard => HWildcard, Binding => HBinding, _}
import picasso.graph.{GT, DiGraph, Automaton, Labeled}
import picasso.utils.Namer
import scala.tools.nsc._

trait DomainSpecificOperations {
  self: AnalysisUniverse =>

  import global._
  import global.definitions._

  var operations: List[Operations] = Nil
  def allOperations = "Operations are: " + operations.map(_.name).mkString("",", ","")

  //TODO explain what is going on here

  /** extending that trait provides unapply for process and expression conversion */
  abstract class Operations {

    def name: String

    //automatically add the class inheriting this trait to operations
    operations = this :: operations

    def process: PartialFunction[Tree, PProcess]
    def expression: PartialFunction[Tree, Expression]
    def removeMarking(a: AgentDefinition[PC]): Option[AgentDefinition[PC]]
    def edgeToGraph: PartialFunction[(PClass, PC, PProcess, PC, Map[PC, Set[ID]]), Seq[PartialDBT]]

  }

}
