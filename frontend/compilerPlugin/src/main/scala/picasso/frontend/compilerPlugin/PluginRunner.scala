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

  override protected def loadRoughPluginsList = List(picasso)

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
    )
    phs foreach (addToPhasesSet _).tupled
  }
  
  override protected def computePluginPhases(): Unit = {
    assert(loadPlugins.length == 1)
    val phs =
      if(picasso.stopBeforeAnalysis) picasso.pluginPhases dropRight 1
      else picasso.pluginPhases
    phs foreach (addToPhasesSet _).tupled
  }

}

object PluginRunner {

  //TODO encapsulate the counter-example displaying and ...

  val name = "picasso"
  val version = "0.1"
  val usage = name + " TODO ..."

  def run[A](rsc: (PluginRunner, Settings, CompilerCommand), fct: PluginRunner => A): A = {
    val runner = rsc._1
    val command = rsc._3
    val run = new runner.Run
    run.compile(command.files)
    fct(runner)
  }

  def makeRunner(args: Array[String]) = {
    //TODO makes option friendlier (e.g. transform automatically "-debug" into "-P:picasso:debug" )
    val settings = new Settings
    settings.classpath.value = System.getProperty("java.class.path")

    val command = new CompilerCommand(args.toList, settings) {
      override val cmdName = "picasso"
    }

    if (!command.ok) Logger.logAndThrow("Plugin", LogError, "!command.ok")
    
    val runner = new PluginRunner(settings)

    (runner, settings, command)
  }
  
  def makeRunnerCP(args: Array[String], compilerClassPath: List[String]) = {
    val settings = new Settings
    settings.classpath.tryToSet(compilerClassPath) 
    val command = new CompilerCommand(args.toList, settings) 
    if (!command.ok) Logger.logAndThrow("Plugin", LogError, "!command.ok")
    val runner = new PluginRunner(settings)
    (runner, settings, command)
  }

  def testCoverComputation(args: Array[String], compilerClassPath: List[String]) = {
    run(makeRunnerCP(args, compilerClassPath), _.picasso.testForTermination)
  }
  
  def testAssert(args: Array[String], compilerClassPath: List[String]) =  {
    run(makeRunnerCP(args, compilerClassPath), _.picasso.testForError)
  }
  
  def testParseOnly(args: Array[String], compilerClassPath: List[String]) =  {
    run(makeRunnerCP(args, compilerClassPath), (_ => ()))
  }

  def main(args: Array[String]) {
    val (r, s, c) = makeRunner(args)
    
    if (s.version.value) {
      println(name + " version " + version)
      return()
    }
    
    if (s.help.value) {
      println(usage)
      println(r.pluginOptionsHelp)
      return()
    }
    
    val result = run((r,s,c), _.picasso.testForError)
    if (result.isDefined) println("error found")
    else println("no error found")
  }

}
