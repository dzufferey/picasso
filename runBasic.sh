#!/bin/sh
export JAVA_OPTS="-Xmx1536M -Xms256M -Xss64M"
scala_version=scala-2.9.1
BASEDIR=`dirname $0`
cp="$HOME/.sbt/boot/$scala_version/lib/*:$BASEDIR/target/${scala_version}/classes:$BASEDIR/lib/*"

#normal version
exec java -cp ${cp} picasso.frontend.basic.Main $*

#-Xprof for profilnig
#exec java -Xprof -cp ${cp} picasso.frontend.basic.Main $*

