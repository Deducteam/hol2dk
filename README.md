Export HOL-Light proofs to Dedukti, Lambdapi and Coq
====================================================

This project provides a tool, hol2dk, to translate [HOL-Light](https://github.com/jrh13/hol-light) proofs to [Dedukti](https://github.com/Deducteam/Dedukti/), [Lambdapi](https://github.com/Deducteam/lambdapi) and [Coq](https://coq.inria.fr/).

[HOL-Light](https://github.com/jrh13/hol-light) is a proof assistant
based on higher-order logic, aka simple type theory.

[Dedukti](https://github.com/Deducteam/Dedukti/) is a proof format
based on the λΠ-calculus modulo rewriting (λ-calculus + simple types +
dependent types + implicit type equivalence modulo user-defined
rewriting rules).

[Lambdapi](https://github.com/Deducteam/lambdapi) is a proof assistant
based on the λΠ-calculus modulo rewriting that can read and generate
Dedukti proofs.

[Coq](https://coq.inria.fr/) is a proof assistant based on the
Calculus of Inductive Constructions.

Results
-------

The HOL-Light base library `hol.ml` and small libraries like
`Arithmetic` and `Logic` can be exported and translated to Dedukti,
Lambdapi and Coq in a few minutes. The generated Dedukti files can be
checked in a few minutes as well, but it takes much longer for Coq to
check the generated files (about 50 minutes with 32 processors for
`hol.ml`).

For bigger libraries like `Multivariate`, it takes even more time for
Coq. For instance, the `Multivariate` library up to `topology.ml` can
be translated to Lambdapi in 18 minutes, then to Coq in 18 more
minutes, but the verification of the generated files by Coq, without
the mapping of real numbers, takes 8 hours with 32 processors.

Usability of translated libraries
---------------------------------

For the obtained theorems to be readily usable in Coq, we need to
align the type and functions of HOL-Light with those used in the Coq
standard library. We already did this for various types including the
types of natural numbers, lists, real numbers and integers, but more
types and functions need to be aligned. The correctness of the
mappings for types defined before real numbers (e.g. natural numbers
and lists) is proved in
[HOLLight_Real.v](https://github.com/Deducteam/coq-hol-light-real/blob/main/HOLLight_Real.v). The
correctness of the mappings for the other types, including real
numbers, is proved here in
[HOLLight.v](https://github.com/Deducteam/hol2dk/blob/main/HOLLight.v).

The resulting theorems are gathered in the Opam package
[coq-hol-light](https://github.com/Deducteam/coq-hol-light) available
in the Coq Opam repository
[released](https://github.com/coq/opam). For the moment, it only
contains about 700 theorems on logic, natural numbers and lists. Much
more theorems will be added soon (the Multivariate library has more
than 40,000 theorems on analysis).

Coq axioms used to encode HOL-Light proofs
------------------------------------------

HOL-Light is based on classical higher-order logic with functional and propositional extensionality. We use the following Coq axioms to encode them:
```
Axiom classic : forall P:Prop, P \/ ~ P.
Axiom constructive_indefinite_description : forall (A : Type) (P : A->Prop), (exists x, P x) -> { x : A | P x }.
Axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, (f x) = (g x)) -> f = g.
Axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q.
Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
```

Bibliography
------------

- [Translating HOL-Light proofs to Coq](https://files.inria.fr/blanqui/lpar24.pdf), Frédéric Blanqui, 4 April 2024

Installing HOL-Light sources
----------------------------

**Requirements:**
- hol-light = ea45176 (07/02/24)
- ocaml = 4.14.2
- camlp5 = 8.02.01
- ocamlfind
- zarith, which may require pkg-config and libgmp-dev
- libipc-system-simple-perl
- libstring-shellquote

Find other potential working ocaml-camlp5 pairs on
https://github.com/jrh13/hol-light/pull/71 .

If you don't already have the HOL-Light sources somewhere, you can
install them by using the following commands:

```
cd $HOME
sudo apt-get install -y libipc-system-simple-perl libstring-shellquote-perl pkg-config libgmp-dev opam
opam init
opam switch create ocaml.4.14.2
eval `opam env`
opam install ocamlfind zarith camlp5.8.02.01
git clone https://github.com/jrh13/hol-light
git checkout ea45176
make -C hol-light
```

Installing hol2dk
-----------------

**Requirements:**
- ocaml >= 4.13
- dune >= 3.7

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

Translating HOL-Light proofs to Lambdapi and Coq
------------------------------------------------

**Requirements:**
- lambdapi commit >= c24b28e2 (28/11/24) > 2.5.1
- [coq-hol-light-real](https://github.com/Deducteam/coq-hol-light-real)
- [coq-fourcolor-reals](https://github.com/coq-community/fourcolor/blob/master/coq-fourcolor-reals.opam)
- coq >= 8.19

For not cluttering HOL-Light sources with the many generated files, we suggest to proceed as follows. For instance, for generating the proofs of the `Logic` library, do:
```
cd $HOLLIGHT_DIR/Logic
hol2dk dump-simp make.ml
mkdir -p ~/output-hol2dk/Logic
cd ~/output-hol2dk/Logic
hol2dk link Logic/make.ml HOLLight_Real.HOLLight_Real --root-path $HOL2DK/HOLLight.v Rdefinitions Rbasic_fun Raxioms
```
This will create files and add links to files needed to generate, translate and check proofs.

You can then do in order:
- `make` to get the list of targets and variables
- `make split` to generate a file for each theorem
- `make -j$jobs lp` to translate HOL-Light proofs to Lambdapi
- `make -j$jobs lpo` to check Lambdapi files (optional)
- `make -j$jobs v` to translate Lambdapi files to Coq files
- `make -j$jobs vo` to check Coq files

To speed up lp file generation for some theorems with very big proofs, you can write in a file called `BIG_FILES` a list of theorem names (lines starting with `#` are ignored). See for instance [BIG_FILES](https://github.com/Deducteam/hol2dk/blob/main/BIG_FILES). You can also change the default values of the options `--max-proof-size` and `--max-abbrev-size` as follows:
- `make -j$jobs MAX_PROOF=500_000 MAX_ABBREV=2_000_000 lp`

Remark: for the checking of generated Coq files to not fail because of lack of RAM, we generate for each theorem `${thm}.lp` one or several files for its proof, and a file `${thm}_spec.lp` declaring this theorem as an axiom. Moreover, each other theorem proof using `${thm}` requires `${thm}_spec` instead of `${thm}`. 

Performance with the mapping of real numbers (master branch)
------------------------------------------------------------

On a machine with 32 processors i9-13950HX and 128G RAM with HOL-Light ea45176, Hol2dk master, OCaml 4.14.2, Camlp5 8.02.01, Lambdapi c24b28e2 and Coq 8.20.0:

| HOL-Light file               | dump  | size   | steps | thms  | lp     | v      | size  | vo     |
|------------------------------|-------|--------|-------|-------|--------|--------|-------|--------|
| hol.ml                       | 3m57s | 3 Gb   | 3 M   | 5687  | 39s    | 34s    | 1 Gb  | 56m23s |
| Multivariate/make_complex.ml | 2h48m | 158 Gb | 90 M  | 41883 | 52m26s | 31m39s | 94 Gb | ~60h   |

Performance without the mapping of real numbers (hol2dk 2.0)
------------------------------------------------------------

On a machine with 32 processors i9-13950HX and 64G RAM, with HOL-Light ea45176, Hol2dk 2.0, OCaml 4.14.2, Camlp5 8.02.01, Lambdapi 2.5.0 and Coq 8.19.1:

| HOL-Light file                     | simp  | size   | steps | thms  | lp     | v      | size  | vo     |
|------------------------------------|-------|--------|-------|-------|--------|--------|-------|--------|
| hol.ml                             | 3m57s | 3 Gb   | 3 M   | 5687  | 51s    | 55s    | 1 Gb  | 18m4s  |
| Multivariate/make_upto_topology.ml | 48m   | 52 Gb  | 52 M  | 18866 | 22m22s | 20m16s | 68 Gb | 8h (*) |
| Multivariate/make_complex.ml       | 2h48m | 158 Gb | 90 M  | 41883 | 52m26s | 31m39s |       |        |

(*) with `make -j32 vo; make -j8 vo`

Translating HOL-Light proofs to Dedukti
---------------------------------------

Requirement: dedukti 2.7

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

Alignments of HOL-Light types and definitions with those of Coq standard library
--------------------------------------------------------------------------------

While it is possible to translate any HOL-Light library to Coq, the
obtained theorems may not be directly applicable by Coq users because
HOL-Light types and functions may not be aligned with those of the Coq
standard library yet. Currently, only the following types and
functions have been aligned with those of Coq:

- unit type
- product type constructor
- type of natural numbers
- functions and predicates on natural numbers: addition, multiplication, order, power, maximum, minimum, substraction, factorial, division, division remainder, parity
- sum type constructor
- option type constructor
- type of lists
- functions on lists
- type of reals
- basic functions and predicates on reals

The part of HOL-Light that is aligned with Coq is gathered in the package
[coq-hol-light](https://github.com/Deducteam/coq-hol-light) available
in the Coq Opam repository [released](https://github.com/coq/opam).

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
- `xci.ml`: slightly truncated version of the HOL-Light file `hol.ml` used for testing.

Note that all these files can be used in the OCaml toplevel as well by removing the `open` instructions and by adding `unset_jrh_lexer;;` and `set_jrh_lexer;;` at the beginning and at the end of the file.

Files necessary for the export to Coq: `encoding.lp`, `erasing.lp`, `renaming.lp`, `HOLLight.v`.

Generated file types
--------------------

b.prf: proof steps

b.sig: signature (types, constants, axioms, definitions)

b.thm: map from proof step index to theorem name

b.thp: map every useful theorem index to its name and position (similar to f.thm but with position)

f.nbp: number of proof steps

f.pos: array providing the positions in b.prf of each proof step index

f.use: array lastuse such that lastuse.(i) = 0 if i is a named theorem, the highest proof step index using i if there is one, and -1 otherwise

n.sti: starting index (in f.prf) of theorem n

n.siz: estimation of the size of the proof of n

`n_part_k.idx`: min and max index (in n.prf) of part k proof steps

n.max: array of max proof step indexes of each part of n

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

thmpart f `n_part_k.lp`: reads f.sig, f.thp, f.prf, n.pos, n.use, n.sti, n.max, `n_part_k.idx`, and generates `n_part_k.lp`, `n_part_k.brv`, `n_part_k.brp`, `n_part_k_term_abbrevs_part_i.min`, `n_part_k_subterms.lp`

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
