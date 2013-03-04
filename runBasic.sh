#!/bin/bash
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version=scala-2.9.3
BASEDIR=`dirname $0`
cp="$HOME/.sbt/boot/$scala_version/lib/*:$BASEDIR/core/target/${scala_version}/classes:$BASEDIR/frontend/basic/target/${scala_version}/classes:$HOME/.ivy2/cache/org.apache.commons/commons-lang3/jars/*:$BASEDIR/core/lib/*"

#normal version
exec java -cp ${cp} picasso.frontend.basic.Main $*

#for profiling
#exec java -Xprof -cp ${cp} picasso.frontend.basic.Main $*
#exec java -Xrunhprof:cpu=times   -cp ${cp} picasso.frontend.basic.Main $*
#exec java -Xrunhprof:cpu=samples -cp ${cp} picasso.frontend.basic.Main $*

