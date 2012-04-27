name := "Picasso: basic frontend"

version := "0.1"

organization := "at.ac.ist"

scalaVersion := "2.9.2"

libraryDependencies ++=  Seq(
    "org.scalatest" % "scalatest_2.9.2" % "1.6.1" % "test"
)

mainClass in (Compile, packageBin) := Some("picasso.frontend.basic.Main")

scalacOptions ++= Seq("-unchecked", "-deprecation")

parallelExecution in Test := false

logBuffered in Test := false

