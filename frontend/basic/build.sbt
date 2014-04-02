name := "Picasso: basic frontend"

version := "0.1"

organization := "at.ac.ist"

scalaVersion := "2.10.4"

libraryDependencies ++=  Seq(
    "org.scalatest" % "scalatest_2.10" % "2.0.M5b" % "test"
)

mainClass in (Compile, packageBin) := Some("picasso.frontend.basic.Main")

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

parallelExecution in Test := false

logBuffered in Test := false

