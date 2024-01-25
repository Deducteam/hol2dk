Export HOL-Light proofs to Dedukti, Lambdapi and Coq
====================================================

This project provides a tool to translate [HOL-Light](https://github.com/jrh13/hol-light) proofs to [Dedukti](https://github.com/Deducteam/Dedukti/), [Lambdapi](https://github.com/Deducteam/lambdapi) and [Coq](https://coq.inria.fr/).

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

The HOL-Light base library `hol.ml` and the libraries `Arithmetic` and
`Logic` formalizing the metatheory of first-order logic can be
exported and translated to Dedukti, Lambdapi and Coq in a few
minutes. The generated Dedukti files can be checked in a few minutes
also, but it takes a much longer time for Coq to check the generated
files (28 minutes for `hol.ml`), and too much memory for Lambdapi.

On the other hand, `hol2dk` may take several hours to translate the
proofs of a few particular theorems of the `Multivariate` library:
`GRASSMANN_PLUCKER_4`, `CHAIN_BOUNDARY_BOUNDARY` and
`HOMOTOPIC_IMP_HOMOLOGOUS_REL_CHAIN_MAPS`, because their proofs
contain a lot of big terms without sharing. We will work on improving
this.

Finally, while it is possible to translate any HOL-Light proof to Coq,
the translated theorem may not be directly usable by Coq users because
HOL-Light types and functions may not be aligned with those of the Coq
standard library yet. Currently, only the type of natural numbers and
various functions on natural numbers have been aligned. We gathered
the obtained 448 lemmas in the package
[coq-hol-light](https://github.com/Deducteam/coq-hol-light) available
in the Coq Opam repository [released](https://github.com/coq/opam). We
are working on adding more mappings (lists, reals).

Installing HOL-Light sources
----------------------------

**Requirements:**
- hol-light >= af186e9f3c685f5acab16097b05717c10ebb030d (28/01/23)
- libipc-system-simple-perl
- libstring-shellquote
- ocaml 4.14.1
- camlp5 8.00.05
- ocamlfind
- num

Find other potential working ocaml-camlp5 pairs on
https://github.com/jrh13/hol-light/pull/71 .

If you don't already have the HOL-Light sources somewhere, you can
install them by using the following commands:

```
cd $HOME
sudo apt-get install -y libipc-system-simple-perl libstring-shellquote-perl opam
opam init
opam switch create ocaml.4.14.1
eval `opam env`
opam install ocamlfind num camlp5
git clone --depth 1 -b master https://github.com/jrh13/hol-light
make -C hol-light
```

Installing hol2dk
-----------------

**Requirements:**
- ocaml >= 4.13
- dune >= 3.7

hol2dk is now available on [Opam](https://opam.ocaml.org/). To install it, simply do:
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

Patching HOL-Light sources
--------------------------

By default, HOL-Light does not generate proofs that can be checked independently. Therefore, it must be patched so that proof steps are recorded:

```
$HOL2DK_DIR/patch $HOLLIGHT_DIR
```

This script slightly modifies a few HOL-Light files in order to dump proofs:
- `fusion.ml`: the HOL-Light kernel file defining types, terms, theorems, proofs and proof rules
- `bool.ml`: HOL-Light file defining basic tactics corresponding to introduction and elimination rules of connectives
- `equal.ml`: HOL-Light file defining basic tactics on equality

The patch also adds a file `xnames.ml`.

Before applying the patch, a copy of these files is created in `fusion-bak.ml`, `bool-bak.ml`, etc.

To restore HOL-Light files, simply do:
```
$HOL2DK_DIR/unpatch $HOLLIGHT_DIR
```
You can add the option `-y` to force file restoration.

Summary of hol2dk commands
--------------------------

Get it by running `hol2dk` without arguments.

Dumping HOL-Light proofs
------------------------

For dumping the proofs of a HOL-Light file depending on `hol.ml` do:
```
cd $HOLLIGHT_DIR
hol2dk dump-simp file.ml
```

This will generate the following files:
- `file.sig`: constants
- `file.prf`: theorems (proof steps)
- `file.thm`: named theorems
- `file.pos`: positions of proof steps in `file.prf`
- `file.use`: data about the use of theorems

WARNING: it is important to run the command in the HOL-Light directory so as to compute the list of named theorems properly.

For dumping (a subset of) `hol.ml` do:
```
cd $HOLLIGHT_DIR
hol2dk dump-simp-use file.ml
```
where `file.ml` should at least contain the contents of `hol.ml` until the line `loads "fusion.ml";;`.

The command `dump-simp` (and similarly for `dump-simp-use`) are actually the sequential composition of various lower level commands: `dump`, `pos`, `use`, `rewrite` and `purge`:

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

The command `purge` compute in `file.use` all the theorems that do not need to be translated.

The command `simp` is the sequential composition of `rewrite` and `purge`.

Generating dk/lp files from dumped files
--------------------------------------

The base Dedukti/Lambdapi theories in which HOL-Light proofs are translated is described in the files [theory_hol.lp](https://github.com/Deducteam/hol2dk/blob/main/theory_hol.lp) and [theory_hol.dk](https://github.com/Deducteam/hol2dk/blob/main/theory_hol.dk) respectively.

You can then generate `file.dk` with:
```
hol2dk file.dk
```

And `file.lp` with:

```
hol2dk file.lp
```

It is possible to get the proof of a single theorem by giving its
number as additional argument (useful for debugging):

```
hol2dk file.lp $theorem_number
```

Generating dk/lp files in parallel
----------------------------------

Dk/lp file generation is linear in the size of dumped files. For big
dumped files, we provide two different commands to do file generation
in parallel using `make`: `mk` and `split`. Currently, only `mk`
allows to generate dk files, but `split` generate lp and coq files
that are faster to check.

Remark: for not cluttering HOL-Light sources with generated files, we suggest to proceed as follows. For instance, for generating the proofs for `hol.ml`:
```
cd $HOLLIGHT_DIR
hol2dk dump-simp-use hol.ml
mkdir -p ~/output-hol2dk/hol
cd ~/output-hol2dk/hol
$HOL2DK_DIR/add-links hol
```
This will add links to files that are needed to generate, translate and check proofs.

**By generating a lp file for each named theorem: command `split`**

```
hol2dk split file
```
generates file.thp and files t.sti, t.pos and t.use for each named theorem t.

You can then generate and check the lp and coq files as follows:
```
make BASE=file -j $jobs lp # generate lp files
make BASE=file mklp # generate lp.mk (lp files dependencies)
make BASE=file -j $jobs lpo # check lp files
make BASE=file -j $jobs v # generate v files
make BASE=file mkv # generate coq.mk (v files dependencies)
make BASE=file -j $jobs vo # check v files
```

**By splitting proofs in several parts: command `mk`**

```
hol2dk mk $nb_parts file
```
generates `file.dg` and `file.mk`.

Then generate and check `file.dk` with:

```
make -f file.mk -j $jobs dk
```

And `file.lp` with:

```
make -f file.mk -j $jobs lp
```

Checking the generated dk file
------------------------------

**Requirement:** dedukti >= 2.7, [kocheck](https://github.com/01mf02/kontroli-rs), or lambdapi >= 2.3.0

Add a link to the dk file defining the logic of HOL-Light:
```
ln -s $HOL2DK_DIR/theory_hol.dk
```

To check the generated dk file with dkcheck, do:
```
dk check file.dk
```

To check the generated dk file with the current version of
[kocheck](https://github.com/01mf02/kontroli-rs), you need to slightly
change the generated file:

```
sed -e 's/^injective /def /g' file.dk > file-for-kocheck.dk
kocheck -j 7 file-for-kocheck.dk
```

Checking the generated lp files
-------------------------------

**Requirement:** lambdapi >= 2.3.0 for single-threaded generated files, lambdapi master branch for multi-threaded generated files

Add links to the following hol2dk files:
```
ln -s $HOL2DK_DIR/theory_hol.lp
ln -s $HOL2DK_DIR/lambdapi.pkg
```

To check the generated lp files with
[lambdapi](https://github.com/Deducteam/lambdapi), you can do:
```
lambdapi check file.lp
```
It is however more efficient to use `make` as explained above.

**Remark:** In case hol-light and lambdapi do not use the same
ocaml versions, it is convenient to use different switches in each
directory:

Xterm 1 (for HOL-Light):
```
cd hol-light
opam switch link 4.02.3
eval `opam env`
```

Xterm 2 (for checking dk/lp files):
```
opam switch link 4.14.1
eval `opam env`
```

Translating lp files to Coq
---------------------------

**Requirement:** lambdapi >= 2.4.1

Add links to the following hol2dk files:
```
ln -s $HOL2DK_DIR/coq.v
ln -s $HOL2DK_DIR/_CoqProject
```

Once HOL-Light files have been translated to Lambdapi files, it is possible
to translate the obtained Lambdapi files into [Coq](https://coq.inria.fr/) files
using the Coq [export](https://lambdapi.readthedocs.io/en/latest/options.html#export) feature of Lambdapi.

If the lp files have been generated using `split`, simply do:
```
make -j $jobs v
```
If the lp files have been generated using `mk`, simply do:
```
make -f file.mk -j $jobs v
```

Otherwise, you need to translate Lambdapi files one by one by hand or
by using a script:
```
lambdapi export -o stt_coq --encoding $HOL2DK_DIR/encoding.lp --erasing $HOL2DK_DIR/erasing.lp --renaming $HOL2DK_DIR/renaming.lp --requiring coq.v file.lp | sed -e 's/hol-light\.//g' > file.v
```

You can then check the generated Coq files as follows.
If the lp files have been generated with `split`, simply do:
```
make -j $jobs vo
```
If the lp files have been generated using `mk`, simply do:
```
make -f file.mk -j $jobs vo
```

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

Alignments of HOL-Light types and definitions with those of Coq
---------------------------------------------------------------

While it is a priori possible to translate any HOL-Light proof to Coq, the
obtained theorems may not be directly usable by Coq users because
HOL-Light types and functions may not be aligned with those of the Coq
standard library yet. Currently, only the following types and
functions have been aligned with those of Coq:

- unit type
- product type constructor
- type of natural numbers
- functions and predicates on natural numbers: addition, multiplication, order, power, maximum, minimum, substraction, factorial, division, division remainder, parity
- option type constructor

The part of HOL-Light that is aligned with Coq is gathered in the package
[coq-hol-light](https://github.com/Deducteam/coq-hol-light) available
in the Coq Opam repository [released](https://github.com/coq/opam).

Performance
-----------

Performance on a machine with 32 processors i9-13950HX and 64G RAM:

Dumping, simplification and translation of `Logic/Make.ml` with `split`:
  * dump-simp 10m29s 10G 83% useless (including hol.ml)
  * lp 57s 1.2G mklp 1m24s
  * v 43s mkv 50s vo (-j20) 34m10s

Dumping and translation of `Logic/make.ml` with `mk 32` (includes `Library/analysis`):
  * dump-simp 11m42s 10G 21.2M steps (83% unused including hol.ml) +1729 named theorems
  * dk 1m13s dko 4m15s lp 42s v 12s vo 1h11m

Dumping, simplification and translation of `Arithmetic/make.ml` with `split`:
  * dump-simp 6m2s 5.4G 82% useless (including hol.ml) 2.5M steps
  * lp 21s 734M mklp 1m6s
  * v 31s 682M mkv 23s vo (-j20) 32m

Dumping of `hol.ml`:
  * checking time without proof dumping: 1m14s
  * checking time with proof dumping: 1m44s (+40%)
  * dumped file size: 3G
  * number of named theorems: 2842
  * number of proof steps: 8.5M (8% unused)
  * simplification time: 1m22s
  * number of simplifications: 1.2M (14%)
  * unused proof steps after simplification: 29%
  * purge time: 11s
  * unused proof steps after purge: 60%

| rule         |  % |
|:-------------|---:|
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

Multi-threaded translation of `hol.ml` to Lambdapi and Coq with `split`:
  * make sti: <1s
  * make -j32 lp: 42s 1.2G
  * make mklp: 39s 2.7M
  * make -j32 lpo: 1h36m 0.9G
  * make -j32 v: 42s 1.1G
  * make mkv: 41s 2.7M
  * make -j16 vo: 32m20s 3.1G

Multi-threaded translation of `hol.ml` to Lambdapi and Coq with `mk 100`:
  * hol2dk mk 100: 14s
  * make -j32 lp: 31s 1.1G type abbrevs 796K term abbrevs 583M (53%)
  * make -j32 lpo: fails (too big for lambdapi)
  * make -j32 v: 24s 1G
  * make -j32 vo: 1h4m

Multi-threaded translation of `hol.ml` to Dedukti with `mk 100`:
  * make -j32 dk: 49s 1.5G type abbrevs 876K term abbrevs 660M (44%)
  * dkcheck: 3m31s
  * kocheck: 5m54s

Single-threaded translation of `hol.ml` to Lambdapi:
  * lp files generation: 4m7s 1.1G type abbrevs 308K term abbrevs 524M (48%)

Single-threaded translation of `hol.ml` to Dedukti:
  * dk files generation: 7m12s 1.4G type abbrevs 348K term abbrevs 590M (42%)

Dumping and translation of `hol.ml` upto `arith.ml` with `mk 7`:
  * proof dumping time: 11s 77M 448 named theorems
  * number of proof steps: 302 K (9% unused)
  * prf simplification: 2s
  * unused proofs after simplification: 31%
  * unused proofs after purge: 66%
  * dk file generation: 1s 29M
  * checking time with dk check: 4s
  * lp file generation: 1s 21M
  * checking time with lambdapi: 31s
  * translation to Coq: 1s 20M
  * checking time for Coq 8.18.0: 1m7s

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

Dumping of `hol.ml`:
  * ocaml cheking without proof dumping: 1m14s
  * ocaml proof dumping: 2m9s (+74%)
  * proof size file: 5.5G
  * number of proof steps: 14.3M

| rule       |  % |
|:-----------|---:|
| refl       | 26 |
| eqmp       | 21 |
| term_subst | 15 |
| trans      | 11 |
| comb       | 10 |
| deduct     |  7 |
| type_subst |  4 |
| abs        |  2 |
| beta       |  2 |
| assume     |  2 |

Dumping of `hol.ml` upto `arith.ml` (by commenting from `loads "wf.ml"` to the end):
  * ocaml proof dumping: 13.2s
  * number of proof steps: 564351
  * proof dumping: 1.4s 157M
  * dk file generation: 45s 153M
  * checking time with dk check: 26s
  * checking time with kocheck -j 7: 22s
  * lp file generation: 29s 107M
  * checking time with lambdapi: 2m49s

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

Files necessary for the export to Coq: `encoding.lp`, `erasing.lp`, `renaming.lp`, `coq.v`.

Thanks
------

HOL-Light proof recording follows
[ProofTrace](https://github.com/jrh13/hol-light/tree/master/ProofTrace)
developed by Stanislas Polu in 2019.
