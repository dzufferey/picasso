import sbt._
import Keys._

object PicassoBuild extends Build {
    
    lazy val root = Project(id = "picasso", base = file(".")) aggregate(core, basic/*, compilerPlugin*/)

    lazy val core = Project(id = "picasso-core", base = file("core"))

    lazy val basic = Project(id = "picasso-basic", base = file("frontend/basic")) dependsOn(core)
    
    //lazy val compilerPlugin = Project(id = "picasso-compilerPlugin", base = file("frontend/compilerPlugin")) dependsOn(core)
}
