#!/bin/bash
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version1=scala-2.10
scala_version2=scala-2.10.1
BASEDIR=`dirname $0`
cp="$HOME/.sbt/boot/$scala_version2/lib/*:$BASEDIR/core/target/${scala_version1}/classes:$BASEDIR/frontend/compilerPlugin/target/${scala_version1}/classes:$HOME/.ivy2/cache/org.apache.commons/commons-lang3/jars/*:$BASEDIR/core/lib/*"

echo not yet ported to scala 2.10!!
#normal version
exec java -cp ${cp} picasso.frontend.compilerPlugin.PluginRunner $*

#example:
#runPlugin.sh -P:picasso:debug -P:picasso:hide=graph src/test/resources/plugin/collection1.scala
