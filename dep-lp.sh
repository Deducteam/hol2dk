#!/bin/sh

f=$1
echo -n "${f}o:"
awk 'BEGIN{FS="[ .;]"}/^require /{printf" %s.lpo",$4;next}/^[^r]/{nextfile}' $f
echo
