#!/bin/bash
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version=scala-2.9.2
BASEDIR=`dirname $0`
cp="$HOME/.sbt/boot/$scala_version/lib/*:$BASEDIR/core/target/${scala_version}/classes:$HOME/.ivy2/cache/org.apache.commons/commons-lang3/jars/*:$BASEDIR/core/lib/*"

exec java -cp ${cp} picasso.frontend.dbpGraph.Main $*
