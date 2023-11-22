TODO
----

- add commands for patch/unpatch/add-links ?

- use a filename different from "dump.ml" and "dump.prf" to allow parallel dumping

- create doc on readthedocs.io

- replace terms of the form (@f _ x) by x if f is a function equal to
  the identity like I, NUMERAL

- replace type variables like _1718 by better names like A

- turn proof_content into a private data type so as to simplify proofs
  on the fly with the following rules:

    trans p (refl _) --> p
    trans (refl _) p --> p
    sym (refl x) --> refl x
    sym (sym p) --> p
    trans (sym p) (sym q) --> or <-- sym (trans q p) ?
    
- add v file checking in ci

- instrument excluded middle in class.ml

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
    
