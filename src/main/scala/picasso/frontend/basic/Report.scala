package picasso.frontend.basic

import picasso.utils._
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
    Console.println("Analysis of \"" + name + "\".\n")
    for (p <- typed orElse parsed.map(_._1)) Console.println("Input Actors:\n\n" + p.mkString("","\n\n","") + "\n")
    for (i <- parsed.map(_._2)) Console.println("Initial Configuration:\n\n" + i + "\n")
    for (a <- agents) Console.println("As CFA:\n\n" + a.mkString("","\n\n","") + "\n")
    for (t <- transitions) Console.println("Transitions:\n\n" + t.mkString("","\n\n","") + "\n")
    for (i <- initConf) Console.println("Initial Configuration:\n\n" + i + "\n")
    for (c <- cover) Console.println("Basis of the covering set:\n\n" + c.mkString("","\n\n","") + "\n")
    for (e <- error) Console.println("ERROR:\n\n" + e)
  }

  def graphvizToSvg(dot: String): String = {
    SysCmd.execWithInputAndGetOutput(Array("dot", "-Tsvg"), Nil, dot) match {
      case Left(bytes) => new String(bytes)
      case Right(err) =>
        Logger("basic", LogWarning, "error running dot (code: "+err+").")
        "<pre>\n" + dot + "\n</pre>"
    }
  }
  
  def makeHtmlReport(fileName: String) = {
    val buffer = new scala.collection.mutable.StringBuilder(100 * 1024)
    buffer ++= "<!DOCTYPE HTML>\n"
    buffer ++= "<html>\n"
    buffer ++= "<head>\n"
    buffer ++= "    <meta charset=\"utf-8\">\n"
    buffer ++= "    <title>Analysis report for "+name+"</title>\n"
    buffer ++= "</head>\n"
    buffer ++= "<body>\n"
    buffer ++= "<h1>Analysis report for "+name+"</h1>\n"
    
    buffer ++= "<h2>Input</h2>\n"
    buffer ++= "<h3>Actors</h3>\n"
    for (p <- typed orElse parsed.map(_._1); a <- p) {
      buffer ++= "<pre>\n" + a + "\n</pre>\n"
    }
    buffer ++= "<h3>Initial Configuration</h3>\n"
    for (i <- parsed.map(_._2)) buffer ++= "<pre>\n" + i + "\n</pre>\n"
    
    buffer ++= "<h2>CFA</h2>\n"
    for (as <- agents) {
      buffer ++= "<ul>\n"
      for (a <- as) {
        buffer ++= "<li>" + graphvizToSvg(Misc.docToString(a.toGraphviz("agent", "digraph", "agt"))) + "\n"
      }
      buffer ++= "</ul>\n"
    }
    
    buffer ++= "<h2>Graph rewriting rules</h2>\n"
    buffer ++= "<h3>Transitions</h3>\n"
    for (ts <- transitions; t <- ts) {
      buffer ++= "<p>"+t.id+"</p>" + "\n"
      buffer ++= graphvizToSvg(Misc.docToString(t.toGraphviz("trs"))) + "\n"
    }
    buffer ++= "<h3>Initial Configuration</h3>\n"
    for (i <- initConf) buffer ++= i.toGraphviz("init") + "\n"

    buffer ++= "<h2>Cover</h2>\n"
    for (cs <- cover) {
      buffer ++= "<ul>\n"
      for (c <- cs) {
        buffer ++= "<li>" + graphvizToSvg(c.toGraphviz("cover")) + "\n"
      }
      buffer ++= "</ul>\n"
    }
    
    for (e <- error) {
      buffer ++= "<h2>ERROR</h2>\n"
      buffer ++= "<pre>\n" + e + "\n</pre>\n"
    }

    buffer ++= "</body>\n"
    buffer ++= "</html>\n"
    IO.writeInFile(fileName, buffer.toString)
  }

}
