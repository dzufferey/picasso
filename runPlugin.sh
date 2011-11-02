#!/bin/sh
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version=scala-2.9.1
BASEDIR=`dirname $0`
cp="$BASEDIR/project/boot/$scala_version/lib/*:$BASEDIR/target/${scala_version}/classes:$BASEDIR/lib/*"

#normal version
exec java -cp ${cp} picasso.frontend.compilerPlugin.PluginRunner $*

#-Xprof for profilnig
#exec java -Xprof -cp ${cp} picasso.frontend.compilerPlugin.PluginRunner $*

#example:
#runPlugin.sh -P:picasso:debug -P:picasso:hide=graph src/test/resources/plugin/collection1.scala
