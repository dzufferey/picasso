package picasso.frontend.basic

import picasso.ast._
import picasso.transform.DBPWrapper
import picasso.model.dbp.DepthBoundedProcess
import picasso.analysis._

class Analysis(_agents: Seq[AgentDefinition[Actors.PC]], _init: picasso.ast.Expression) extends DBPWrapper[Actors.PC](_agents, _init) {
  
  //TODO: check for covering of a given pattern
    
  //compute cover
  def computeCover = {
    val procSimpleForward = new DepthBoundedProcess[DBC](system) with ForwardWithWidening
    procSimpleForward.computeCover(initConf)
  }

  //check for assertion failure and other standard errors
  def testForError = {
    val errorConf = emptyConf + DBCN_Error
    val procSimpleForward = new DepthBoundedProcess[DBC](system) with ForwardWithWidening
    procSimpleForward.forwardCoveringWithTrace(initConf, errorConf)
  }

  //definitions to extends DBPWrapper
  def DBCN[T](l : picasso.math.hol.Literal[T]) = DBCN(l.toString)
  def DBCN_Any = DBCN("Any")
  def DBCN_Name = DBCN("name")
  def DBCN_Unit = DBCN("()")
  def DBCN_Case(uid: String) = DBCN(uid)
  def DBCN_Error = DBCN("error")

}
