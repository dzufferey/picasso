name := "Picasso: Scala compiler plug-in"

version := "0.1"

organization := "at.ac.ist"

scalaVersion := "2.10.1"

libraryDependencies ++=  Seq(
    "org.scalatest" % "scalatest_2.10" % "2.0.M5b" % "test",
    "org.scala-lang" % "scala-compiler" % "2.10.1"
)

mainClass in (Compile, packageBin) := Some("picasso.frontend.compilerPlugin.PluginRunner")

scalacOptions ++= Seq("-unchecked", "-deprecation")

parallelExecution in Test := false

logBuffered in Test := false

