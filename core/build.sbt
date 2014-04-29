name := "Picasso: core components"

version := "0.2"

organization := "at.ac.ist"

scalaVersion := "2.10.4"

libraryDependencies ++=  Seq(
    "org.scalatest" % "scalatest_2.10" % "2.0.M5b" % "test",
    "org.apache.commons" % "commons-lang3" % "3.1",
    "org.ow2.sat4j" % "org.ow2.sat4j.core" % "2.3.4",
    "org.ow2.sat4j" % "org.ow2.sat4j.pb" % "2.3.4",
    "org.ow2.sat4j" % "org.ow2.sat4j.maxsat" % "2.3.4"
)

mainClass in (Compile, packageBin) := Some("picasso.frontend.dbpGraph.Main")

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

parallelExecution in Test := false

logBuffered in Test := false

