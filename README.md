Export HOL-Light proofs to Dedukti, Lambdapi and Rocq
=====================================================

This project provides a tool, hol2dk, to translate [HOL-Light](https://github.com/jrh13/hol-light) proofs to [Dedukti](https://github.com/Deducteam/Dedukti/), [Lambdapi](https://github.com/Deducteam/lambdapi) and [Rocq](https://rocq-prover.org/).

[HOL-Light](https://github.com/jrh13/hol-light) is a proof assistant
based on higher-order logic, aka simple type theory.

[Dedukti](https://github.com/Deducteam/Dedukti/) is a proof format
based on the λΠ-calculus modulo rewriting (λ-calculus + simple types +
dependent types + implicit type equivalence modulo user-defined
rewriting rules).

[Lambdapi](https://github.com/Deducteam/lambdapi) is a proof assistant
based on the λΠ-calculus modulo rewriting that can read and generate
Dedukti proofs.

[Rocq](https://rocq-prover.org/) is a proof assistant based on the
Calculus of Inductive Constructions.

Examples
--------

hol2dk is used to translate to Rocq the
HOL-Light [Multivariate](https://github.com/jrh13/hol-light/blob/master/Multivariate/make_complex.ml)
library of HOL-Light which contains more than 20,000 theorems on
arithmetic, wellfounded relations, lists, real numbers, integers,
basic set theory, permutations, group theory, matroids, metric spaces,
homology, vectors, determinants, topology, convex sets and functions,
paths, polytopes, Brouwer degree, derivatives, Clifford algebra,
integration, measure theory, complex numbers and analysis,
transcendental numbers, real analysis, complex line integrals,
etc. The resulting Rocq theorems are provided in the Opam package
[coq-hol-light](https://github.com/Deducteam/coq-hol-light). Various
HOL-Light types and functions have been mapped to the corresponding
types and functions of the Rocq standard library so that, for
instance, a HOL-Light theorem on HOL-Light real numbers is translated
to a Rocq theorem on Rocq real numbers. The provided theorems can
therefore be readily used within other Rocq developments based on the
Rocq standard library.

hol2dk has also been used to translate to Rocq the HOL-Light
[Logic](https://github.com/jrh13/hol-light/blob/master/Logic/make.ml)
library which also contains many useful functions and results like
unification, resolution, rewriting, LPO, skolemization, the
Löwenheim-Skolem theorems, the compactness theorem, Herbrand's
theorem, Birkhoff's theorem, etc. The resulting Rocq theorems are
provided in the Opam package
[rocq-hollight-logic](https://github.com/Deducteam/rocq-hollight-logic).

Bibliography
------------

- [Translating HOL-Light proofs to Coq](https://doi.org/10.29007/6k4x), Frédéric Blanqui, 25th International Conference on Logic for Programming, Artificial Intelligence and Reasoning (LPAR), 2024.

Dependencies
------------

- ocaml >= 4.13
- hol_light >= 3.0.0
- lambdapi >= 3.0.0
- rocq >= 9.0

Installing HOL-Light sources
----------------------------

```
opam install -y --deps-only hol_light.3.0.0
git clone https://github.com/jrh13/hol-light
make -C hol-light
```

Installing hol2dk
-----------------

hol2dk is available on [Opam](https://opam.ocaml.org/). To install it, simply do:
```
opam install hol2dk
```

You can also install hol2dk from its sources as follows:
```
git clone https://github.com/Deducteam/hol2dk.git
cd hol2dk
dune build && dune install
```

Setting the environment variables `$HOLLIGHT_DIR` and `$HOL2DK_DIR`
----------------------------------------------------------------------

For some commands to have access to files in hol2dk sources, you need
to set the following environment variables:
```
export HOLLIGHT_DIR=   # absolute path to hol-light source directory
export HOL2DK_DIR=     # absolute path to hol2dk source directory
```

In case you installed hol2dk using opam, write:
```
export HOL2DK_DIR=$OPAM_SWITCH_PREFIX/share/hol2dk
```

Summary of hol2dk commands
--------------------------

Get it by running `hol2dk | less`.

Patching HOL-Light sources
--------------------------

By default, HOL-Light does not generate proofs that can be checked independently. Therefore, it must be patched so that proof steps are recorded:

```
hol2dk patch
```

This command slightly modifies a few HOL-Light files in order to dump proofs:
- `fusion.ml`: the HOL-Light kernel file defining types, terms, theorems, proofs and proof rules
- `bool.ml`: HOL-Light file defining basic tactics corresponding to introduction and elimination rules of connectives
- `equal.ml`: HOL-Light file defining basic tactics on equality

The patch also adds a file `xnames.ml`.

Before applying the patch, a copy of these files is created in `fusion-bak.ml`, `bool-bak.ml`, etc.

To restore HOL-Light files, simply do:
```
hol2dk unpatch
```

Dumping HOL-Light proofs
------------------------

For dumping the proofs of a HOL-Light file depending on `hol.ml` do:
```
cd $HOLLIGHT_DIR
hol2dk dump-simp [$path/]file.ml
```

This will generate the following files:
- `[$path/]file.sig`: constants
- `[$path/]file.prf`: theorems (proof steps)
- `[$path/]file.thm`: named theorems
- `[$path/]file.pos`: positions of proof steps in `file.prf`
- `[$path/]file.use`: data about the use of theorems

WARNING: it is important to run the command in `$HOLLIGHT_DIR` so as to compute the list of named theorems properly.

For dumping (a subset of) `hol.ml` do:
```
cd $HOLLIGHT_DIR
hol2dk dump-simp-before-hol file.ml
```
where `file.ml` should at least contain the contents of `hol.ml` until the line `loads "fusion.ml";;`.

The command `dump-simp` (and similarly for `dump-simp-before-hol`) are actually the sequential composition of various lower level commands: `dump`, `pos`, `use`, `rewrite` and `purge`:

**Simplifying dumped proofs.** HOL-Light proofs have many detours that can be simplified following simple rewrite rules. For instance, s(u)=s(u) is sometimes proved by MK_COMB from s=s and u=u, while it can be directly proved by REFL.

The command `rewrite` implements the following simplification rules:
- SYM(REFL(t)) ⟶ REFL(t)
- SYM(SYM(p)) ⟶ p
- TRANS(REFL(t),p) ⟶ p
- TRANS(p,REFL(t)) ⟶ p
- CONJUNCT1(CONJ(p,_)) ⟶ p
- CONJUNCT2(CONJ(_,p)) ⟶ p
- MKCOMB(REFL(t),REFL(u)) ⟶ REFL(t(u))
- EQMP(REFL _,p) ⟶ p

**Purging dumped proofs.** Because HOL-Light tactics may fail, some theorems are generated but not used in the end, especially after simplification. Therefore, they do not need to be translated.

The command `purge` compute in `file.use` all the theorems that do not need to be translated. For instance, in the HOL-Light base library `hol.ml`, 60% of proof steps are useless after simplication.

The command `simp` is the sequential composition of `rewrite` and `purge`.

Translating HOL-Light proofs to Lambdapi and Rocq
-------------------------------------------------

- create a directory where all files will be generated:
```
mkdir output
```

- configure the directory with all the required files:
```
cd output
hol2dk config $hollight_file.ml $root_path [rocq_file_or_module] ... [$mapping.mk] [$mapping.lp]
```
Do `hol2dk config` to get more details.

- You can then do in order:
  * `make` to get the list of targets and variables
  * `make split` to generate a file for each theorem
  * `make -j$jobs lp` to translate HOL-Light proofs to Lambdapi
  * `make -j$jobs lpo` to check Lambdapi files (optional)
  * `make -j$jobs v` to translate Lambdapi files to Rocq files
  * `make -j$jobs merge-spec-files` to merge all small spec files into a single one
  * `make -j$jobs rm-empty-deps` to remove `theory_hol.v`, `${base}_types.v` and `${base}_axioms.v` (to use when these files are empty only)
  * `make -j$jobs vo` to check Rocq files

To speed up lp file generation for some theorems with very big proofs, you can write in a file named `BIG_FILES` a list of theorem names (lines starting with `#` are ignored). See for instance [BIG_FILES](https://github.com/Deducteam/hol2dk/blob/main/BIG_FILES). You can also change the default values of the options `--max-proof-size` and `--max-abbrev-size` by writing `make MAX_PROOF=500_000 MAX_ABBREV=2_000_000`.

**Remark:** for the checking of generated Rocq files to not fail because of lack of RAM, we generate for each theorem `${thm}.lp` one or several files for its proof, and a file `${thm}_spec.lp` declaring this theorem as an axiom. Moreover, each other theorem proof using `${thm}` requires `${thm}_spec` instead of `${thm}`.

Performances
------------

On a machine with 32 processors i9-13950HX, 128 Gb RAM, Hol2dk master, HOL-Light 3.0.0, OCaml 5.2.1, Camlp5 8.03.01, Lambdapi 83cf0be2, Coq 8.20.0, using the Coq type N for HOL-Light natural numbers:

| HOL-Light file               | dump  | size   | steps | thms  | lp  | v   | size  | vo     |
|------------------------------|-------|--------|-------|-------|-----|-----|-------|--------|
| hol.ml                       | 4m    | 3 Gb   | 3 M   | 5687  | 40s | 37s | 1 Gb  | 10m23s |
| Multivariate/make_complex.ml | 2h30m | 135 Gb | 85 M  | 40728 | 45m | 24m | 91 Gb | 21h14m |

using `make -j32 lp`, `make -j32 v`, `make -j32 merge-spec-files; make -j32 rm-empty-deps; make -j32 -k vo`.

Translating HOL-Light proofs to Dedukti
---------------------------------------

**Requirement:** dedukti 2.7

The Makefile commands above are not implemented for Dedukti yet. It is however possible to translate HOL-Light proofs to Dedukti in parallel by using the following older and less efficient commands:

```
hol2dk mk $nb_parts $base
make -f $base.mk -j$jobs dk
```
where `$base` is the base name of the library, e.g. `make` for `$HOLLIGHT_DIR/Logic/make`, which is also written in the file named `BASE` that is created when you do `hol2dk link Logic/make`.

It generates a single big Dedukti file `$base.dk`. To check it with [dkcheck](https://github.com/Deducteam/Dedukti/) version >= 2.7, simply do:
```
dk check $base.dk
```
To check it with [kocheck](https://github.com/01mf02/kontroli-rs), simply do:
```
kocheck -j$jobs file-for-kocheck.dk
```

Performances: hol.dk can be checked by dkcheck in 4m11s.

Getting statistics on proofs
----------------------------

It is possible to get statistics on proofs by using the command `stat`. For instance, for `hol.ml`, after simplification, we get:

| rule       |  % |
|:-----------|---:|
| comb       | 20 |
| term_subst | 17 |
| refl       | 16 |
| eqmp       | 12 |
| trans      |  9 |
| conjunct1  |  6 |
| abs        |  3 |
| beta       |  3 |
| mp         |  3 |
| sym        |  2 |
| deduct     |  2 |
| type_subst |  2 |
| assume     |  1 |
| conjunct2  |  1 |
| disch      |  1 |
| spec       |  1 |
| disj_cases |  1 |
| conj       |  1 |

Exporting pure Q0 proofs
------------------------

Hol2dk instruments basic HOL-Light tactics corresponding to
introduction and elimination rules of connectives to get smaller
proofs and proofs closer to natural deduction proofs. It is however
possible to generate full Q0 proofs by doing after patching:

```
cd $HOLLIGHT_DIR
sed -i -e 's/.*Q0.*//' -e 's/START_ND*)//' -e 's/(*END_ND//' fusion.ml bool.ml equal.ml
```

Thanks
------

HOL-Light proof recording improves
[ProofTrace](https://github.com/jrh13/hol-light/tree/master/ProofTrace)
developed by Stanislas Polu in 2019.

Source files
------------

Modified HOL-Light files:
- `lib.ml`: provides functions on lists, etc. required by `fusion.ml`. A few lines are commented out so that it compiles with ocamlc.
- `fusion.ml`: defines types, terms, theorems, proofs and elementary proof rules.
- `bool.ml`: defines basic tactics corresponding to introduction and elimination rules of connectives.
- `equal.ml`: defines basic tactic(al)s on equality including alpha and beta-reduction.
These files contain special comments that are removed to patch hol-light.

Additional files required for `hol2dk`:
- `main.ml`: main program of Hol2dk.
- `xprelude.ml`: provides a few basic definitions.
- `xlib.ml`: functions on types, terms and other data structures.
- `xproof.ml`: functions for accessing proofs.
- `xlp.ml`: translation to Lambdapi of types, terms and proofs.
- `xdk.ml`: translation to Dedukti of types, terms and proofs.
- `xfiles.ml`: functions to compute dependencies and theorems of HOL-Light files.
- `xnames.ml`: functions for dumping the index of named theorems.

Note that all these files can be used in the OCaml toplevel as well by removing the `open` instructions and by adding `unset_jrh_lexer;;` and `set_jrh_lexer;;` at the beginning and at the end of the file.

Files necessary for the export to Coq: all the lp and v files.

Generated file types
--------------------

b.prf: proof steps

b.sig: signature (types, constants, axioms, definitions)

b.thm: map from theorem indexes having a name to their name

b.thp: map every useful theorem index to its position in b.prf and the lp filename where its proof is translated

f.nbp: number of proof steps

f.pos: array providing the positions in b.prf of each theorem index

f.use: array lastuse such that lastuse.(i) = 0 if i is a named theorem, the highest theorem index using i if there is one, and -1 otherwise

n.sti: starting index (in f.prf) of theorem n

n.siz: estimation of the size of the proof of n

`n_part_k.idx`: min and max index (in n.prf) of part k proof steps

n.max: array of max theorem indexes of each part of n

n.typ: map from type expression strings to digests and number of type variables

n.sed: sed script to replace type expression digests by type abbreviations

n.brv: ordered list of pairs (term, term abbreviation number)

n.brp: array of positions in the file n.brv

`n_term_abbrevs_part_i.min`: min and max term abbreviation number of part i

`f_types.lp`: types

`f_type_abbrevs.lp`: type abbreviations

`f_terms.lp`: function symbols (i.e. signature)

`f_axioms.lp`: axioms

main hol2dk commands
--------------------

dump f.ml: generates an ml file and call ocaml on it to check f.ml and generates f.prf, f.nbp, f.sig and f.thm

dump-simp f.ml: calls the commands dump f.ml, pos f, use f, and simp f

pos f: reads f.nbp and f.prf, and generates f.pos

use f: reads f.nbp, f.thm and f.prf, and generates f.use

simp f: calls the commands rewrite f and purge f

rewrite f: reads f.pos, f.use and f.prf, and generates a new version of f.prf where proofs have been simplified

purge f: reads f.pos, f.prf, f.thm and f.use, and generates a new file f.use where useless proof steps are mapped to -1

split f: reads f.pos, f.use and f.thm, generates f.thp and, for each useful theorem n (if it has no user-defined name, we use its index as name), n.nbp, n.sti, n.pos, n.use

thmsize f n.lp: reads f.prf, n.use, n.pos, n.sti, and generates n.siz

thmsplit f n.lp: reads f.sig, f.thp, f.prf, n.use, n.sti, n.siz, n.pos, and generates the files `n_part_k.idx`, n.max and n.lp

thmpart f `n_part_k.lp`: reads f.sig, f.thp, f.prf, n.pos, n.use, n.sti, n.max, `n_part_k.idx`, and generates `n_part_k.lp`, `n_part_k.brv`, `n_part_k.brp`, `n_part_k_term_abbrevs_part_i.min`, `n_part_k_term_abbrevs_part_i.max`, `n_part_k_subterms.lp`

theorem f n.lp: reads f.sig, f.thp, f.prf, n.pos, n.use, n.sti, and generates the files `n_part_k_proofs.lp`, `n_proofs.lp`, `n.typ`, `n_term_abbrevs.lp`, `n_subterm_abbrevs.lp`, `n_term_abbrevs.typ`, `n_part_k_deps.lp`, `n_part_k.lp`.

abbrev f `n_term_abbrevs_part_i.lp`: reads f.sig, f.thp, n.brv, n.brp, `n_term_abbrevs_part_i.min`, and generates `n_term_abbrevs_part_i.typ` and `n_term_abbrevs_part_i.lp`

`type_abbrevs` f: for each file n.typ in the current directory, reads n.typ and generates n.sed and `f_type_abbrevs.lp`

Makefile targets for generating Lambdapi files
----------------------------------------------

split: calls hol2dk command split

lp:
- generates `f_types.lp`, `f_type_abbrevs.lp`, `f_terms.lp`, `f_axioms.lp`
- for every big file n.lp, calls hol2dk thmsize f n.lp (generates the file n.siz) and hol2dk thmsplit f n.lp (generates the files `n_part_k.idx`, n.max and n.lp)
- calls the Makefile target lp-proofs
- calls the Makefile target lp-abbrevs
- calls hol2dk type_abbrevs f
- calls the Makefile target rename-abbrevs

lp-proofs:
- for each file `n_part_k.idx` (big file part), calls hol2dk thmpart f `n_part_k.lp`
- for each file n.sti for which there is no file n.lp yet (small files), calls hol2dk theorem f n.lp

lp-abbrevs: for each file n.min, calls hol2dk abbrev f n.lp

rename-abbrevs: for each file n.sed, apply n.sed to n.lp
