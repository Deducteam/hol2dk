#!/bin/sh

f=$1
echo -n "${f}o:"
awk 'BEGIN{FS="[ .]"}/^Require /{printf" %s.vo",$3;next}/^[^R]/{nextfile}' $f
echo
