NOTES
-----

## 05/03/24

Gulliver: 56 processors Intel Core Processor (Haswell, no TSX) 2.3 Ghz cache 16 Mo, RAM 122 Go

hol.ml: dump-simp-use 6m7s split 2s make -j56 lp 1m14s v 45s dep-lpo 1m46s vo 38m46s

Multivariate/make_upto_topology.ml: dump-simp 1h55m36s split 13s make -j56 lp

## 04/03/24

The generation of `URYSOHN_LEMMA.lp` takes 6m30s. `URYSOHN_LEMMA_term_abbrevs.lp` has 100_000 abbreviations. Compilation of the corresponding Coq files depending on `--max-abbrevs`:

| max-abbrevs | term_abbrevs.v | URYSOHN_LEMMA.v |
|-------------|----------------|-----------------|
| 50_000      | 5m48s          | 20m40s          |
| 10_000      | 1m4s           | 21m33s          |
| 5_000       | 35s            | 21m27s          |

## 02/02/24

Translation of `Multivariate/make.ml` upto `topology.ml`:
  * lp 6h40m 25G v 13m7s 21G mklp 2m24s mkv 1s
  * vo -j16 256m + -j8 50m + -j4 181m + -j1 134m
    Stack overflow on big term_abbrevs.v files below + URYSOHN_LEMMA_term_abbrevs.v (722M)
    (100,000 < nb defs < 600,000)

## 25/01/24

By introducing sharing in term abbreviations, we can reduce the size of some lp files significantly:

| term_abbrevs.lp file                    | generation | size w/o sharing | size w/ sharing | %    |
|-----------------------------------------|------------|------------------|-----------------|------|
| CHAIN_BOUNDARY_BOUNDARY                 | 56m29s     | 5.2G             | 1.9G            | -63% |
| GRASSMANN_PLUCKER_4                     | 3h25m27s   | 14G              | 4.7G            | -66% |
| HOMOTOPIC_IMP_HOMOLOGOUS_REL_CHAIN_MAPS | 6h48m57s   | 19G              | 5.3G            | -72% |

but coq checking is slowed down: the checking of `hol.ml` takes 40m29s 3.5G with sharing and -j16 (it fails now with -j20) instead of 32m20s 3.1G with -j20 before.

statistics on hashtables for CHAIN_BOUNDARY_BOUNDARY:
  we need to improve the hash function on big terms

string: 362_900 bindings, 262_144 buckets, 1.38 bindings/bucket, max 10
buckets with 0 bindings: 65_814 (25% of buckets)

| bindings | buckets | %   | cumulated | % bindings |
|----------|---------|-----|-----------|------------|
| 1        | 90_480  | 24% | 90_480    | 24%        |
| 2        | 63_195  | 34% | 216_870   | 59%        |
| 3        | 29_063  | 24% | 304_059   | 83%        |
| 4        | 10_028  | 11% | 344_171   | 94%        |
| 5        | 2_823   | 3%  | 358_286   | 98%        |
| 6        | 598     | 0%  | 361_874   | 99%        |
| 7        | 124     | 0%  | 362_742   | 99%        |
| 8        | 14      | 0%  | 362_854   | 99%        |
| 9        | 4       | 0%  | 362_890   | 99%        |
| 10       | 1       | 0%  | 362_900   | 100%       |

type: 371 bindings, 131_072 buckets, 0.00 bindings/bucket, max 9
buckets with 0 bindings: 130_759 (99% of buckets)

| bindings | buckets | %   | cumulated | % bindings |
|----------|---------|-----|-----------|------------|
| 1        | 278     | 74% | 278       | 74%        |
| 2        | 24      | 12% | 326       | 87%        |
| 3        | 5       | 4%  | 341       | 91%        |
| 4        | 4       | 4%  | 357       | 96%        |
| 5        | 1       | 1%  | 362       | 97%        |
| 6        | 0       | 0%  | 362       | 97%        |
| 7        | 0       | 0%  | 362       | 97%        |
| 8        | 0       | 0%  | 362       | 97%        |
| 9        | 1       | 2%  | 371       | 100%       |

term: 382_063 bindings, 1_048_576 buckets, 0.36 bindings/bucket, max 46_266
buckets with 0 bindings: 1_024_846 (97% of buckets)

| bindings | buckets | %  | cumulated | % bindings |
|----------|---------|----|-----------|------------|
| 1        | 17_769  | 4% | 17_769    | 4%         |
| 2        | 2_855   | 1% | 23_479    | 6%         |
| 3        | 976     | 0% | 26_407    | 6%         |
| 4        | 602     | 0% | 28_815    | 7%         |
| 5        | 287     | 0% | 30_250    | 7%         |
| 6        | 253     | 0% | 31_768    | 8%         |
| 7        | 134     | 0% | 32_706    | 8%         |
| 8        | 111     | 0% | 33_594    | 8%         |
| 9        | 85      | 0% | 34_359    | 8%         |
| 10       | 69      | 0% | 35_049    | 9%         |

type_abbrev: 121 bindings, 131_072 buckets, 0.00 bindings/bucket, max 3
buckets with 0 bindings: 130_957 (99% of buckets)

| bindings | buckets | %   | cumulated | % bindings |
|----------|---------|-----|-----------|------------|
| 1        | 110     | 90% | 110       | 90%        |
| 2        | 4       | 6%  | 118       | 97%        |
| 3        | 1       | 2%  | 121       | 100%       |

term_abbrev: 265_885 bindings, 1_048_576 buckets, 0.25 bindings/bucket, max 41_447
buckets with 0 bindings: 1_043_364 (99% of buckets)

| bindings | buckets | %  | cumulated | % bindings |
|----------|---------|----|-----------|------------|
| 1        | 3_522   | 1% | 3_522     | 1%         |
| 2        | 870     | 0% | 5_262     | 1%         |
| 3        | 222     | 0% | 5_928     | 2%         |
| 4        | 165     | 0% | 6_588     | 2%         |
| 5        | 55      | 0% | 6_863     | 2%         |
| 6        | 44      | 0% | 7_127     | 2%         |
| 7        | 20      | 0% | 7_267     | 2%         |
| 8        | 21      | 0% | 7_435     | 2%         |
| 9        | 22      | 0% | 7_633     | 2%         |
| 10       | 32      | 0% | 7_953     | 2%         |

subterms: 363_160 bindings, 1_048_576 buckets, 0.35 bindings/bucket, max 178
buckets with 0 bindings: 742_670 (70% of buckets)

| bindings | buckets | %   | cumulated | % bindings |
|----------|---------|-----|-----------|------------|
| 1        | 255_762 | 70% | 255_762   | 70%        |
| 2        | 44_486  | 24% | 344_734   | 94%        |
| 3        | 5_130   | 4%  | 360_124   | 99%        |
| 4        | 459     | 0%  | 361_960   | 99%        |
| 5        | 32      | 0%  | 362_120   | 99%        |
| 6        | 10      | 0%  | 362_180   | 99%        |
| 7        | 4       | 0%  | 362_208   | 99%        |
| 8        | 4       | 0%  | 362_240   | 99%        |
| 9        | 0       | 0%  | 362_240   | 99%        |
| 10       | 2       | 0%  | 362_260   | 99%        |

## 19/01/24

Arithmetic/make:
- dump-simp 6m2s 5.4G 82% useless
- lp 21s 734M
- v 31s 682M mkv 23s vo (-j20) 32m

## 17/01/24

the generation of Multivariate/make_upto_topology/GRASSMANN_PLUCKER_4.lp takes too much memory

the problem comes from the fact that the term abbreviations in this file are too big

a solution is to use (maximal) sharing when building the map of term abbreviations

but sharing increases generation time significantly

with split and -j32, hol.lp is generated in 40s instead of 32s (+25%)

in singly-threaded mode, hol.lp is generated in 4m59s instead of 4m7s (+21%)

however GRASSMANN_PLUCKER_4.lp can now be generated in 2 hours (119m23s)

`Multivariate/make_upto_topology.ml`:
  * lp 4h28m 48G type_abbrevs 47M term_abbrevs 42G with 38G by 3 files >1G:
    - GRASSMANN_PLUCKER_4_term_abbrevs.lp 14G
    - CHAIN_BOUNDARY_BOUNDARY_term_abbrevs.lp 5.2G
    - HOMOTOPIC_IMP_HOMOLOGOUS_REL_CHAIN_MAPS_term_abbrevs.lp 19G

## 11/01/24

Translation of `hol.ml` with splitting: stp <1s lp 32s 1.1G v 43s 1.1G mkv 51s 2.7M vo (-j20) 28m 3.1G mklp 47s 2.7M lpo (-j32) 96m 0.9G

## 20/12/23

Some theorems are created with no name but are used later. See for instance `pth` in `bool.ml`:
```
let EQT_INTRO =
  let t = `t:bool` in
  let pth =
    let th1 = DEDUCT_ANTISYM_RULE (ASSUME t) TRUTH in
    let th2 = EQT_ELIM(ASSUME(concl th1)) in
    DEDUCT_ANTISYM_RULE th2 th1 in
  (*REMOVE pth: |- t = (t = T) *)
  fun th -> EQ_MP (INST[concl th,t] pth) th;;
```

## 06/12/23

Translation of `100/isoperimetric.ml`:
  * dump 44m23s 153 Go 223 M steps +17166 named theorems (half of all HOL-Light named theorems)
  * pos 13m51s 1.9 Go
  * use 13m54s 1 Go 7% unused
  * rewrite 1h17m - pos&use = 49m 14% simplifications 29% unused
  * purge 21m31s 59% useless
  * dg 100 15m5s
  * too big to be translated to dk/lp

Translation of `Multivariate/make.ml`:
  * dump 35m52s 120 Go +16646 named theorems
  * dump-simp 133 minutes (59% useless)

Translation of `Multivariate/make_upto_derivatives.ml`:
  * dump 27m46s 91 Go + 14901 named theorems

Translation of `Multivariate/make_upto_topology.ml`:
  * dump 15m55s 48 Go +11987 named theorems 89 M steps
  * pos 4m15s, use 4m18s 7% unused
  * rewrite 24m43s -pos&use = 16m 14% simplifications 28% unused
  * purge 3m37 58% useless, dg 100 4m55s
  * too big to be translated to dk/lp

## 27/11/23

- results on new computer with 32 * 13th Gen Intel(R) Core(TM) i9-13950HX:
  * hol.ml dg 100 j 32: lp 48s v 39s vo 175m18s

## before 14/10/23

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
