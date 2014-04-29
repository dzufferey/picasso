#!/bin/bash
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version1=scala-2.10
scala_version2=scala-2.10.3
BASEDIR=`dirname $0`
scala="$HOME/.sbt/boot/$scala_version2/lib/*:$BASEDIR/core/target/${scala_version1}/classes"
sat4j="$HOME/.ivy2/cache/org.ow2.sat4j/org.ow2.sat4j.core/jars/*:$HOME/.ivy2/cache/org.ow2.sat4j/org.ow2.sat4j.pb/jars/*:$HOME/.ivy2/cache/org.ow2.sat4j/org.ow2.sat4j.maxsar/jars/*"
cp="$scala:$HOME/.ivy2/cache/org.apache.commons/commons-lang3/jars/*:$sat4j"

exec java -cp ${cp} picasso.frontend.dbpGraph.Main $*
