package picasso.frontend.compilerPlugin

import scala.tools.nsc.{Global, Settings, SubComponent, CompilerCommand}
import scala.tools.nsc.reporters.{ConsoleReporter, Reporter}
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Level, Misc, IO, SysCmd}

/** This class is a compiler that will be used for running
 *  the plugin in standalone mode.
 */
class PluginRunner(settings: Settings, reporter: Reporter) extends Global(settings, reporter) {
  def this(settings: Settings) = this(settings, new ConsoleReporter(settings))

  val picasso = new PicassoPlugin(this)

  /** The phases to be run. */
  override protected def computeInternalPhases() {
    val phs = List(
      syntaxAnalyzer          -> "parse source into ASTs, perform simple desugaring",
      analyzer.namerFactory   -> "resolve names, attach symbols to named trees",
      analyzer.packageObjects -> "load package objects",
      analyzer.typerFactory   -> "the meat and potatoes: type the trees",
      superAccessors          -> "add super accessors in traits and nested classes",
      pickler                 -> "serialize symbol tables",
      refchecks               -> "reference and override checking, translate nested objects",
      //what about liftCode ?? probably don't need this anyway ...
      uncurry                 -> "uncurry, translate function values to anonymous classes",
      tailCalls               -> "replace tail calls by jumps"
      //The following phase of the compiler explicitOuter transforms pattern match, so we stop there ...
    ) ::: {
      val zipped = picasso.components zip picasso.descriptions
      if(picasso.stopBeforeAnalysis) zipped take (zipped.length -1)
      else zipped
    }
    phs foreach (addToPhasesSet _).tupled
  }

}

object PluginRunner {

  //TODO encapsulate the counter-example displaying and ...

  val name = "picasso"
  val version = "0.1"
  val usage = "TODO ..."

  def runWithSettings[A](args: Array[String], settings: Settings, fct: PluginRunner => A): A = {
    val command = new CompilerCommand(args.toList, settings) {
      override val cmdName = "picasso"
    }

    if (!command.ok) Logger.logAndThrow("Plugin", LogError, "!command.ok")

    val runner = new PluginRunner(settings)
    val run = new runner.Run
    run.compile(command.files)

    fct(runner)
  }

  def testCoverComputation(args: Array[String], compilerClassPath: List[String]) = {
    val settings = new Settings
    settings.classpath.tryToSet(compilerClassPath) 
    runWithSettings(args, settings, _.picasso.testForTermination)
  }
  
  def testAssert(args: Array[String], compilerClassPath: List[String]) =  {
    val settings = new Settings
    settings.classpath.tryToSet(compilerClassPath) 
    runWithSettings(args, settings, _.picasso.testForError)
  }
  
  def testParseOnly(args: Array[String], compilerClassPath: List[String]) =  {
    val settings = new Settings
    settings.classpath.tryToSet(compilerClassPath) 
    runWithSettings(args, settings, (_ => ()))
  }

  def main(args: Array[String]) {
    val settings = new Settings
    
    if (settings.version.value) {
      println(name + " version " + version)
      return()
    }
    
    if (settings.help.value) {
      println(usage)
      return()
    }
    
    val result = runWithSettings(args, settings, _.picasso.testForError)
    if (result.isDefined) println("error found")
    else println("no error found")
  }

}
