package picasso.frontend.compilerPlugin

import picasso.utils.{LogDebug, Logger, IO}

object PluginSuiteCommon {
  
  //add the compiler to the CP
  val configFile = "frontend/compilerPlugin/build.sbt" //build.scala.versions=scalaVersion
  lazy val scalaVersion = {
    val values = IO.readTextFile(configFile)
    val pre = values.indexOf("scalaVersion")
    val start = values.indexOf("\"", pre) + 1
    val end = values.indexOf( "\"", start)
    values.substring(start, end)
  }
  lazy val scalaVersionDot = scalaVersion.replace("-",".")
  lazy val scalaLib = sys.env("HOME") + "/.ivy2/cache/org.scala-lang/scala-library/jars/scala-library-"+scalaVersionDot+".jar"
  val compilerCP = List(scalaLib +
                        ":frontend/compilerPlugin/target/scala-"+scalaVersionDot+"/classes/"
                       )

  //assumes that the pwd the project root (where sbt is run)
  val testDir = "frontend/compilerPlugin/src/test/resources/plugin/"

  def runPluginCover(filesNames: List[String], options: List[String] = Nil) = {
    //Console.println("cp = " + compilerCP)
    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(LogDebug)
    Logger.disallow("graph")
    try  {
      val files = filesNames map (testDir + _ + ".scala")
      assert(PluginRunner.testCoverComputation((options ::: files).toArray, compilerCP))
    } finally {
      Logger.setMinPriority(previousLog)
      Logger.allow("graph")
    }
  }
  
  def runPluginError(filesNames: List[String], options: List[String] = Nil): Boolean = {
    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(LogDebug)
    Logger.disallow("graph")
    Logger.disallow("Analysis")
    try  {
      val files = filesNames map (testDir + _ + ".scala")
      PluginRunner.testAssert((options ::: files).toArray, compilerCP).isDefined //otherwise would return a trace
    } finally {
      Logger.setMinPriority(previousLog)
      Logger.allow("graph")
      Logger.allow("Analysis")
    }
  }

  def runPluginParse(filesNames: List[String], options: List[String] = Nil) = {
    //Console.println("cp = " + compilerCP)
    val previousLog = Logger.getMinPriority
    Logger.setMinPriority(LogDebug)
    try  {
      val files = filesNames map (testDir + _ + ".scala")
      PluginRunner.testParseOnly((options ::: files).toArray, compilerCP)
    } finally {
      Logger.setMinPriority(previousLog)
    }
  }

}
