#!/bin/sh
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version=scala-2.9.1
BASEDIR=`dirname $0`
cp="$HOME/.sbt/boot/$scala_version/lib/*:$BASEDIR/target/${scala_version}/classes:$HOME/.ivy2/cache/org.sat4j/org.sat4j.core/jars/*"

#normal version
exec java -cp ${cp} picasso.frontend.basic.Main $*

#for profiling
#exec java -Xprof -cp ${cp} picasso.frontend.basic.Main $*
#exec java -Xrunhprof:cpu=times   -cp ${cp} picasso.frontend.basic.Main $*
#exec java -Xrunhprof:cpu=samples -cp ${cp} picasso.frontend.basic.Main $*

