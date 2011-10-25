name := "Picasso"

version := "0.1"

organization := "at.ac.ist"

scalaVersion := "2.9.1"

libraryDependencies +=  "org.scalatest" % "scalatest_2.9.1" % "1.6.1" % "test"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.9.1"

scalacOptions ++= Seq("-unchecked", "-deprecation")

parallelExecution in Test := false

logBuffered in Test := false

