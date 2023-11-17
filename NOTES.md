NOTES
-----

- dumping files after hol.ml:
  * 100/bertrand: 2m13s 14M steps 4.8 Go
  * 100/isoperimetric:

- results on new computer with 32 * 13th Gen Intel(R) Core(TM) i9-13950HX:
  * hol.ml dg 100 j 32: lp 48s v 39s vo 175m18s

- instrumenting BETA_CONV reduces the number of proof steps of `hol.ml` by 0.1% only

- instrumenting SYM reduces the number of proof steps of `hol.ml` by 4%

- replacing ALPHA by REFL reduces the number of proof steps of `hol_upto_arith` from 405621 to 324391 (-20%)!

- doing dk/lp generation of arith.ml in parallel:
  * lp file generation: 7s 69 Mo
  * checking time with lambdapi: 1m51s

- translation of hol.ml:
  * ocaml checking: 1m23s
  * proof checking + dumping: 1m54s (+37%) 3.8 Go 11 Mo proof steps
  * stats computation: 25s
  * dk generation: 26m47s 3.6 Go

- effect of instrumenting intro/elim rules:

    * number of proof steps: 408777 instead of 564351 (-28%)
    * dk file generation: 22s 99 Mo instead of 45s 153 Mo (-51% and -35%)
    * checking time with dk check: 14s instead of 26s (-46%)
    * checking time with kocheck -j 7: 23s instead of 22s
    * lp file generation: 14s 69 Mo instead of 29s 107 Mo (-51% and -35%)
    * checking time with lambdapi: 2m instead of 2m49s (-29%)

- removing private for hol_type and term increases generation time!
  for arith.lp we get 33s instead of 31s

- generating dk/lp output with a compiled program is faster:

  for arith.ml we get:
    * for dk: 48s instead of 2m6s (-62%)
    * for lp: 29s instead of 1m6 (-56%)

- dumping proofs is fast:
  * arith.ml: 157 Mo in 1.4s
  * hol.ml: 5.5 Go in 2m30s

- generate type abbreviations recursively for types (typex = fun typey
  typez) doesn't seem worthwhile

- making terms more implicit make lambdapi slow down

- effect of sharing types and terms on arith.ml:

    * time of lp file generation: 1m6s instead of 59s (+12%)
    * size of lp files: 103 Mo instead of 217 Mo (-52%)
    * checking time with lambdapi: 3m1s instead of 5m46s (-48%)

  when split in 3 dk files:
  
    * time of dk file generation: 2m08s instead of 1m33s (+38%)
    * size of dk files: 265 Mo instead of 360 Mo (-26%)
      101 Mo (38%) are used by name qualifications
    * checking time with dk check: 40s instead of 1m12s (-44%)
    * checking time with kocheck -j 7: 42s instead of 50s (-16%)

  when in a single dk file:

    * time of dk file generation: 2m6s instead of 1m33s (+35%)
    * size of dk file: 153 Mo instead of 360 Mo (-57%)
    * checking time with dk check: 26s instead of 1m12s (-64%)
    * checking time with kocheck -j 7: 22s instead of 50s (-56%)

- the proof of `! p q. p ==> q ==> p /\ q` requires 263 proof steps
  and generates a lp file of 43482 octets

```
g `! p q. p ==> q ==> p /\ q`;;
e GEN_TAC;;
e GEN_TAC;;
e (DISCH_THEN (LABEL_TAC "p"));;
e (DISCH_THEN (LABEL_TAC "q"));;
e CONJ_TAC;;
e (USE_THEN "p" ACCEPT_TAC);;
e (USE_THEN "q" ACCEPT_TAC);;
top_thm();;
```

- 100/isoperimetric.ml takes 35m to check by ocaml, and requires
  355,603,071 proof steps

- It is currently not efficient to generate a lp file for each proof
  step because the loading mechanism of Lambdapi is not adapted.

Indeed, if a.lp requires b.lp, and b.lp requires c.lp then, when
loading b.lpo, c.lpo is also loaded: loading is recursive. This is due
to the fact that a term in b could contain symbols in c.

With files generated from HOL-Light proof steps, this is however not
the case. Indeed, suppose that thm-x.lp requires theory.lp (definition
of all function symbols) and thm-y.lp. Perhaps thm-y.lp itself has
other dependencies but we do not need to load them because theorems
are opaque: we just need their type which depends on theory.lp only.

This means that the loading mechanism of Lambdapi should be improved
so that a module is loaded only if its symbols are actually necessary.

- use of elementary proof rules from fusion.ml using `gl ' REFL[ ;(]'|wc -l`:

```
REFL 147
TRANS 360
MK_COMB 115
BETA 12
ASSUME 319
EQ_MP 246
DEDUCT_ANTISYM_RULE 23
INST_TYPE 48
INST 326
```

- Q0 rules used for checking arith.ml using `print_proof_stats()`:

number of proof steps: 564351

```
      refl    141216 25%
     trans     46124  8%
      comb     54623 10%
       abs     11173  2%
      beta     17012  3%
    assume     20658  4%
      eqmp    131186 23%
    deduct     42028  7%
term_subst     79941 14%
type_subst     20318  4%
     axiom         9  0%
   sym_def        58  0%
  type_def         6  0%
```

- replacing
```
type thm = Sequent (term list * term * int)
```
by
```
type thm = term list * term * int
```

does not improve checking time of hol.ml
- with Sequent: 1m54s
- without Sequence: 1m55s
