package picasso.frontend.compilerPlugin

import scala.tools.nsc
import scala.tools.nsc.{Global,Phase}
import scala.tools.nsc.plugins.{Plugin,PluginComponent}
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin.transform._

/** This class is the entry point for the plugin. */
class PicassoPlugin(val global: Global) extends Plugin {
  import global._
  val name = "picasso"
  val description = "Software modelchecker for program using actors."

  var stopBeforeAnalysis    = false
  var experimental          = false


  sealed abstract class OptKind(val option: String, val description: String) 
  case class NoArgOpt(opt: String, descr: String, action: () => Unit) extends OptKind(opt, descr)
  case class OneArgOpt(opt: String, descr: String, action: String => Unit) extends OptKind(opt, descr)
  case class ManyArgOpt(opt: String, descr: String, action: Seq[String] => Unit) extends OptKind(opt, descr)
    
  private val oneArg = "smth"
  private val manyArgs = "a,b,..."
  private val optPrefix = "  "
  private val optSpaces = 28

  def opts = List(
    NoArgOpt("parse", "Checks only whether the program is something we can handle (stop after parsing)", (() => stopBeforeAnalysis = true)),
    NoArgOpt("error", "Only error messages", (() => Logger.setMinPriority(LogError))),
    NoArgOpt("quiet", "Warning and error messages", (() => Logger.setMinPriority(LogWarning))),
    NoArgOpt("info", "More verbose", (() => Logger.setMinPriority(LogInfo))),
    NoArgOpt("debug", "Most verbose", (() => Logger.setMinPriority(LogDebug))),
    ManyArgOpt("hide", "Removes the ouput comming from " + manyArgs, ( args => args foreach (Logger.disallow))),
    NoArgOpt("XP", "Enable experimental features",  (() => experimental = true))
  )

  def fullOption(opt: String) = "-P:"+name+":"+opt

  private def printOpt(o: OptKind) = {
    val start = o match {
      case NoArgOpt(o, _, _) => fullOption(o)
      case OneArgOpt(o, _, _) => fullOption(o) + "=" + oneArg
      case ManyArgOpt(o, _, _) => fullOption(o) + "=" + manyArgs
    }
    val middle = (0 until (optSpaces - start.length)).map(_ => ' ').mkString
    val end = o.description
    optPrefix + start + middle + end
  }

  /** The help message displaying the options for that plugin. */
  override val optionsHelp: Option[String] = {
    val help = opts.map(printOpt).mkString("","\n","")
    Some(help)
  }

  /** Processes the command-line options. */
  private def splitList(lst: String) : Seq[String] = lst.split(',').map(_.trim).filter(!_.isEmpty)
  private def processOption(option: String) {
    opts.find(o => option startsWith o.option) match {
      case Some(NoArgOpt(_,_,act)) => act()
      case Some(OneArgOpt(o,_,act)) => act(option.substring(o.length + 1))
      case Some(ManyArgOpt(o,_,act)) => act(splitList(option.substring(o.length + 1)))
      case None => Logger("Plugin", LogWarning, "Invalid option (ignoring it): " + option)
    }
  }
  override def processOptions(options: List[String], error: String => Unit) {
    options foreach processOption
  } 

  val analyzer = new Analysis(global, this)

  val pluginPhases =  List(
    new Unfolder(global, this)          -> "flatten nested expressions",
    new LLifter(global, this)           -> "move nested functions/classes to package level",
    new Constructor(global, this)       -> "move initialisation code from definitions to constructor",
    new Link(global, this)              -> "performs some kind of linking to get ride of the inheritance layer",
    new GettersSetters(global, this)    -> "within one class replaces the getters and setters by the appropriate variable access",
    analyzer                            -> "the analysis"
  )

  val components = pluginPhases map (_._1)

  def testForTermination = analyzer.testForPossibleTerminationUsingFullCover
  def testForError = analyzer.testForError

}

