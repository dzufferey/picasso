package picasso.frontend.basic

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.math._
import picasso.ast._

class Report(name: String) {

  //TODO timestamps

  protected var parsed: Option[(Iterable[Actor], Expression)] = None
  def setParsed(p: (Iterable[Actor], Expression)) = {
    parsed = Some(p)
  }

  protected var typed: Option[Iterable[Actor]] = None
  def setTyped(t: Iterable[Actor]) = {
    typed = Some(t)
  }

  protected var agents: Option[Iterable[AgentDefinition[Actors.PC]]] = None
  def setAgents(a: Iterable[AgentDefinition[Actors.PC]]) = {
    agents = Some(a)
  }

  protected var transitions: Option[Iterable[Analysis#DBT]] = None
  def setTransitions(t: Iterable[Analysis#DBT]) = {
    transitions = Some(t)
  }

  protected var initConf: Option[Analysis#DBCC] = None
  def setInitConf(i: Analysis#DBCC) = {
    initConf = Some(i)
  }

  protected var cover: Option[Iterable[Analysis#DBCC]] = None
  def setCover(c: Iterable[Analysis#DBCC]) = {
    cover = Some(c)
  }

  protected var error: Option[String] = None
  def setError(err: String) = {
    error = Some(err)
  }

  def makeConsoleReport = {
    sys.error("TODO")
  }
  
  def makeHtmlReport = {
    sys.error("TODO")
  }

}
