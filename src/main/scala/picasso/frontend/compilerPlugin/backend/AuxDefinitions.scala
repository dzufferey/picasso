package picasso.frontend.compilerPlugin.backend

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.frontend.compilerPlugin._
import picasso.ast.{Ident => PIdent, Process => PProcess, _}
import picasso.math.hol.{Type => HType, ClassType => HClassType, Application => HApplication, Bool => HBool, Wildcard => HWildcard, Binding => HBinding, _}
import picasso.graph._
import picasso.model.dbp._
import picasso.math._
import scala.tools.nsc._

trait AuxDefinitions extends DefDBP {
  self: AnalysisUniverse =>
  
  def DBCN[T](l : Literal[T]) = DBCN(l.toString)
  def DBCN_Any = DBCN("Any")

  /** a generic name in the pi-calculus sense. */
  def fresh = DBCN("name")

  def errorState = DBCN("error")
  
  def matchTrueAny = DBCN(DBCS[PC](Set("true","Any")))
  def matchFalseAny = DBCN(DBCS[PC](Set("false","Any")))
  def matchTrueFalseAny = DBCN(DBCS[PC](Set("true","false","Any")))

  ///////////////////////////////////////////////////
  // Additional elements introduced by translation //
  ///////////////////////////////////////////////////
  
  val thisVar = Variable("this") setType Channel() //TODO this should have the type of the class it is associated with
  val thisChannel = ID(thisVar)

  /** Message destination */
  val msgDest = Variable("to") setType Channel()
  
  /** Wrap content + return address into a 'Message' */
  def addReturnAddress(msg: Expression, returnAddress: Expression = thisChannel) = Application("Message", List(returnAddress, msg))
  /** Unwrap a message and match the sender */
  def unpackMessageWithSender(p: Pattern): Pattern = Case("Message", List(PIdent(senderChannel), p))
  /** Unwrap a message without matching the sender */
  def unpackMessageWoSender(p: Pattern): Pattern = Case("Message", List(Wildcard, p))
  
  /** receive, react */
  lazy val senderChannel = ID(Variable("sender") setType typeOfType(senderType))
  /** !? */
  lazy val sendSync = ID(Variable("sendSync") setType typeOfType(senderType))

  //about the return from a fct call
  val retVar = Variable("return") setType Channel() //TODO a better way to type ?
  val retID = ID(retVar)
  val returnIdent = PIdent(retID)

  //about collections
  def defaultCollectionNode = DBCN("collection")
  def collectionMember(collection: Variable) = collection.tpe match {
    case Collection(_, element) => Variable("member") setType element
    case other => Logger.logAndThrow("Plugin", LogError, "collection do not have collection type" + other)
  }

  //////////////////////
  // Needed in PiCode //
  //////////////////////

  /** program counter (states of the automata) */
  type PC = String

  /** Intermediate Automaton: used to get rid of the 'Global' suffs */
  type IA = GT {
    type V = PC
    type VL = Unit
    type EL = PProcess
  }
}
