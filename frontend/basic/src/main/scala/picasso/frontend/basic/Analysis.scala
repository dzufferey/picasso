package picasso.frontend.basic

import picasso.ast._
import picasso.transform.DBPWrapper
import picasso.model.dbp.DepthBoundedProcess
import picasso.analysis._

class Analysis(_agents: Seq[AgentDefinition[Actors.PC]], _init: picasso.ast.Expression) extends DBPWrapper(_agents, _init) {

  //definitions to extends DBPWrapper
  def DBCN[T](l : picasso.math.hol.Literal[T]) = DBCN(l.toString)
  def DBCN_Any = DBCN("Any")
  def DBCN_Name = DBCN("name")
  def DBCN_Unit = DBCN("()")
  def DBCN_Case(uid: String) = DBCN(uid)
  def DBCN_Error = DBCN("error")

}
