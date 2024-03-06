TODO
----

- optimize number of let's (use a let only if an abbreviation is used more than once)

- remove base argument in all commands by using BASE file

- rename file _term by _sig

- keep subterm_abbrevs?

- Makefile: add targets for dk output

- simplify dk output of proofs by replacing [c : x:A -> B := x:A => t] by [c (x:A) : B := t].

- use exact_no_check/vm_cast_no_check/native_cast_no_check in lambdapi export to coq ? can work only if there is no implicit argument and no need for implicit coercions

- improve hash function on big terms

- beta-normalize hol-light terms ?

- remove the need for sed after lambdapi export -o stt_coq

- remove/comment code for mk (i.e. use split as default)

- improve efficiency of code outputing dk/lp (avoid multiple term traversals)

- generate lp.mk and coq.mk at the same time as lp files

- extend split command to dedukti output

- get rid of use file? in pos files, set pos to -1 for unused theorems?

- simplify/purge proofs in parallel?

- create doc on readthedocs.io

- replace terms of the form (@f _ x) by x if f is a function equal to
  the identity like I, NUMERAL

- replace type variables like _1718 by better names like A

- add v file checking in ci

- make export incremental (1 lp file for each ml file)

- make or_elim more implicit ?

- detect invalid lp identifiers

- minimize and clean xprelude.ml

- keep in memory theorems used more than n>1 times ?

- check whether Proof constructor is still useful

- factorize code between dk and lp? using a functor?

- uniformize names between no part and part

hol2dk xci.dk generates
    . `xci_types`
    . `xci_terms`
    . `xci_axioms`
    . `xci_theorems`
    . `xci_proofs`
    . `xci_term_abbrevs`
    . `xci_type_abbrevs`
    . `xci`
(concatenation of previous files)

renaming:
    . `xci_proofs` -> `xci_proofs_1`
    . `xci_term_abbrevs` -> `xci_proofs_1_term_abbrevs`
    . `xci_type_abbrevs` -> `xci_proofs_1_type_abbrevs`
    
hol2dk dg 7 xci && hol2dk mk 7 xci coq.v && make -f xci.mk dk generates
    . `xci_types`
    . `xci_terms`
    . `xci_axioms`
    . `xci_theorems`
    . `xci_part_*`
    . `xci_part_*_term_abbrevs`
    . `xci_part_*_type_abbrevs`
    . `xci`
(concatenation of previous files)

renaming:
    . part -> proofs
    
hol2dk xci.lp generates
    . `xci_types`
    . `xci_terms`
    . `xci_axioms`
    . `xci`
    . `xci_proofs`
    . `xci_term_abbrevs`
    . `xci_type_abbrevs`

hol2dk dg 7 xci && hol2dk mk 7 xci coq.v && make -f xci.mk lp generates
    . `xci_types`
    . `xci_terms`
    . `xci_axioms`
    . `xci`
    . `xci_part_*`
    . `xci_part_*_type_abbrevs`
    . `xci_part_*_term_abbrevs`
    
