TODO
----

- use HOL-Light database functions to get the list of theorems

- do not generate _spec files anymore since we need only one

- merge the commands split and unsplit into a single one

- xnames.ml: define string_of_file as an iterator

- replace variables like _1718 by better names

- always share closed subterms

- automatically rename type names that are used as symbol names too

- is it really useful to compute a canonical type/term?

- add a term abbreviation only if it is used more than once

- why the mapping of ITLIST does not work anymore ?

- write progress in an ocaml program, and estimate time wrt size of files

- use a single term_abbrev file for each theorem, and split it

- pre-compute once and for all the type and term variables of axioms and definitions

- pre-compute the type and term variables of every theorem ?

- compute proof tree sizes in parallel ?

- really remove useless proof steps to save memory (=> use files are not necessary afterwards)

- get rid of use file? in pos files, set pos to -1 for unused theorems?

- record times to generate proofs and term_abbrevs files of each theorem ?

- optimize number of let's (use a let only if an abbreviation is used more than once)

- rename file _term by _sig

- Makefile: add targets for dk output

- simplify dk output of proofs by replacing [c : x:A -> B := x:A => t] by [c (x:A) : B := t].

- use exact_no_check/vm_cast_no_check/native_cast_no_check in lambdapi export to coq ? can work only if there is no implicit argument and no need for implicit coercions

- improve hash function on big terms

- beta-normalize hol-light terms ?

- remove/comment code for mk? (i.e. use split as default)

- improve efficiency of code outputing dk/lp (avoid multiple term traversals)

- extend split command to dedukti output

- simplify/purge proofs in parallel?

- create doc on readthedocs.io

- replace terms of the form (@f _ x) by x if f is a function equal to
  the identity like I, NUMERAL

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
    
