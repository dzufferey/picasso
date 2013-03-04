name := "Picasso: core components"

version := "0.2"

organization := "at.ac.ist"

scalaVersion := "2.9.3"

libraryDependencies ++=  Seq(
    "org.scalatest" % "scalatest_2.9.3-RC2" % "2.0.M5b" % "test",
    "org.apache.commons" % "commons-lang3" % "3.1"
)

mainClass in (Compile, packageBin) := Some("picasso.frontend.dbpGraph.Main")

scalacOptions ++= Seq("-unchecked", "-deprecation")

parallelExecution in Test := false

logBuffered in Test := false

