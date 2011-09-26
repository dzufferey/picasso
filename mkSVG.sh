#!/bin/sh

base=$1
dot -Tsvg $base.classes.dot -o $base.classes.svg
dot -Tsvg $base.conf.dot -o $base.conf.svg
dot -Tsvg $base.cover.dot -o $base.cover.svg
dot -Tsvg $base.trs.dot -o $base.trs.svg
