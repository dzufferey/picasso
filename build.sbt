name := "Picasso"

version := "0.1"

organization := "at.ac.ist"

scalaVersion := "2.9.1"

libraryDependencies ++=  Seq(
    "org.scalatest" % "scalatest_2.9.1" % "1.6.1" % "test",
    "org.scala-lang" % "scala-compiler" % "2.9.1",
    "org.sat4j" % "org.sat4j.core" % "2.3.1",
    "org.apache.commons" % "commons-lang3" % "3.1"
)

mainClass in (Compile, packageBin) := Some("picasso.frontend.basic.Main")

scalacOptions ++= Seq("-unchecked", "-deprecation")

parallelExecution in Test := false

logBuffered in Test := false

