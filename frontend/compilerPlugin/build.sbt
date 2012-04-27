name := "Picasso: Scala compiler plug-in"

version := "0.1"

organization := "at.ac.ist"

scalaVersion := "2.9.2"

libraryDependencies ++=  Seq(
    "org.scalatest" % "scalatest_2.9.2" % "1.6.1" % "test",
    "org.scala-lang" % "scala-compiler" % "2.9.2"
)

mainClass in (Compile, packageBin) := Some("picasso.frontend.compilerPlugin.PluginRunner")

scalacOptions ++= Seq("-unchecked", "-deprecation")

parallelExecution in Test := false

logBuffered in Test := false

