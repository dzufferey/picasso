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
  val description = "Software modelchecker for program sing the actor library."

  var stopBeforeAnalysis    = false
  var tolerant              = false
  var experimental          = false
  var showIDs               = false

  /** The help message displaying the options for that plugin. */
  override val optionsHelp: Option[String] = Some(
    "  -P:picasso:uniqid         When pretty-printing funcheck trees, show identifiers IDs" + "\n" +
    "  -P:picasso:parse          Checks only whether the program is something we can handle" + "\n" +
    "  -P:picasso:tolerant       Silently replace elements that are not supported by \"unknown\"" + "\n" +
    "  -P:picasso:error          Only error messages" + "\n" +
    "  -P:picasso:quiet          Warning and error messages" + "\n" +
    "  -P:picasso:info           More verbose" + "\n" +
    "  -P:picasso:debug          Most verbose" + "\n" +
    "  -P:picasso:XP             Enable weird transformations and other bug-producing features"
  )

  /** Processes the command-line options. */
  private def splitList(lst: String) : Seq[String] = lst.split(':').map(_.trim).filter(!_.isEmpty)
  override def processOptions(options: List[String], error: String => Unit) {
    for(option <- options) {
      option match {
        case "uniqid"   => showIDs = true
        case "parse"    => stopBeforeAnalysis = true
        case "tolerant" => tolerant = true
        case "error"    => Logger.setMinPriority(LogError)
        case "quiet"    => Logger.setMinPriority(LogWarning)
        case "info"     => Logger.setMinPriority(LogInfo)
        case "debug"    => Logger.setMinPriority(LogDebug)
        case "XP"       => experimental = true
        case _          => Logger("Plugin", LogWarning, "Invalid option (ignoring it): " + option)
      }
    }
  } 

  val analyzer = new Analysis(global, this)

  val components = List(
    new Unfolder(global, this),
    new LLifter(global, this),
    new Constructor(global, this),
    new Link(global, this),
    new GettersSetters(global, this),
    analyzer
  )

  val descriptions = List(
    "flatten nested expressions",
    "move nested functions/classes to package level",
    "move initialisation code from definitions to constructor",
    "performs some kind of linking to get ride of the inheritance layer",
    "within one class replaces the getters and setters by the appropriate variable access",
    "the analysis"
  )

  def testForTermination = analyzer.testForPossibleTerminationUsingFullCover
  def testForError = analyzer.testForError

}

