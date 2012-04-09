#!/bin/bash
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version=scala-2.9.1
BASEDIR=`dirname $0`
cp="$HOME/.sbt/boot/$scala_version/lib/*:$BASEDIR/target/${scala_version}/classes:$HOME/.ivy2/cache/org.sat4j/org.sat4j.core/jars/*:$HOME/.ivy2/cache/org.apache.commons/commons-lang3/jars/*:lib/*"

#normal version
exec java -cp ${cp} picasso.frontend.compilerPlugin.PluginRunner $*

#example:
#runPlugin.sh -P:picasso:debug -P:picasso:hide=graph src/test/resources/plugin/collection1.scala
