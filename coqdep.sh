#!/bin/sh

for f in $*
do
    echo -n "${f}o:"
    awk 'BEGIN{FS="[. ]"}/^Require Import /{printf" %s.vo",$3;next}/^Lemma /{nextfile}' $f
    echo
done
