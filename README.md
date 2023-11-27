Export HOL-Light proofs to Dedukti, Lambdapi and Coq
====================================================

This project provides several things:
- scripts `patch` and `unpatch` to (un)patch HOL-Light to dump proofs
- a program `hol2dk` with commands for dumping proofs from HOL-Light, translate those proofs to Dedukti and Lambdapi, and generate Makefile's to translation those proofs to Coq using lambdapi.

[HOL-Light](https://github.com/jrh13/hol-light) is proof assistant
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
sudo apt-get install -y libipc-system-simple-perl libstring-shellquote
-perl opam
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

hol2dk is now available on Opam. To install it, simply do:
```
opam install hol2dk
```

For the moment, we however need hol2dk sources to run some commands
(checking dk/lp files or translating them to coq).

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

```
bash $HOL2DK_DIR/patch $HOLLIGHT_DIR
```

where `$HOLLIGHT_DIR` is the directory where are the sources of HOL-Light.

This script slightly modifies a few HOL-Light files in order to dump proofs:
- `fusion.ml`: the HOL-Light kernel file defining types, terms, theorems, proofs and proof rules
- `bool.ml`: HOL-Light file defining basic tactics corresponding to introduction and elimination rules of connectives
- `equal.ml`: HOL-Light file defining basic tactics on equality

The patch also adds a file `xnames.ml`.

Before applying the patch, a copy of these files is created in `fusion-bak.ml`, `bool-bak.ml`, etc.

To restore HOL-Light files, simply do:
```
bash $HOL2DK_DIR/unpatch $HOLLIGHT_DIR
```
You can add the option `-y` to force file restoration.

Summary of hol2dk commands
--------------------------

Get it by running `hol2dk` without arguments.

Dumping HOL-Light proof steps
-----------------------------

For dumping a HOL-Light file depending on `hol.ml` do:
```
cd $HOLLIGHT_DIR
hol2dk dump file.ml
```

This will generate the files `file.sig`, `file.prf` and `file.thm`.

WARNING: it is important to run `hol2dk dump` in the HOL-Light directory so as to compute the list of named theorems properly.

For dumping (a subset of) `hol.ml` do:
```
cd $HOLLIGHT_DIR
hol2dk dump-use file.ml
```
where `file.ml` should at least contain the contents of `hol.ml` until the line `loads "fusion.ml";;`.

Once you have generate `file.prf`, you need to generate the files `file.pos` and `file.use` with:
```
hol2dk pos file
hol2dk use file
```

`file.pos` contains the position in `file.prf` of each proof step.

`file.use` contains data to know whether a proof step is actually useful and needs to be translated. Indeed, since HOL-Light tactics may fail, some proof steps are generated but are not used in the end. Therefore, they do not need to be translated.

Simplifying dumped proofs
-------------------------

HOL-Light proofs are often overly complicated and can be simplified following simple rewrite rules. For instance, s(u)=s(u) can be derived by MK_COMB from s=s and u=u, while it can be directly proved by REFL.

Simplification rules currently implemented:
- SYM(REFL(t)) --> REFL(t)
- SYM(SYM(p)) --> p
- TRANS(REFL(t),p) --> p
- TRANS(p,REFL(t)) --> p
- CONJUNCT1(CONJ(p,_)) --> p
- CONJUNCT2(CONJ(_,p)) --> p
- MKCOMB(REFL(t),REFL(u)) --> REFL(t(u))

To simplify `file.prf` and recompute `file.pos` and `file.use` do:
```
hol2dk simp file
```

Generating dk/lp files from dumped files
--------------------------------------

The base theory in which HOL-Light proofs are translated is described in the files [theory_hol.lp](https://github.com/Deducteam/hol2dk/blob/main/theory_hol.lp) and [theory_hol.dk](https://github.com/Deducteam/hol2dk/blob/main/theory_hol.dk).


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
----------------------------------------

Dk/lp file generation is linear in the size of dumped files. For big
dumped files, we provide a command to do file generation in parallel
using `make`.

First generate `file.dg` and `file.mk` with:
```
hol2dk dg $nb_parts file
hol2dk mk file
```
where `$nb_parts` is the number of files in which you want to split the proofs.

Then generate `file.dk` with:

```
make -j $jobs -f file.mk dk
```

And `file.lp` with:

```
make -j $jobs -f file.mk lp
```

Remark: for not cluttering your HOL-Light sources with generated files, we suggest to proceed as follows. For instance, for generating the proofs for `hol.ml`:
```
cd $HOME
mkdir output-hol2dk
cd output-hol2dk
bash $HOL2DK_DIR/add-links hol
cd hol
hol2dk dg 100 hol
hol2dk mk hol
ln -s hol.mk Makefile
make -j32 lp
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
[lambdapi](https://github.com/Deducteam/lambdapi), do:
```
lambdapi check file.lp
```

**Remark:** In case hol-light and dkcheck/lambdapi do not use the same
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

Translating lp files to Coq files
---------------------------------

**Requirement:** lambdapi >= 2.4.1

Add links to the following hol2dk files:
```
ln -s $HOL2DK_DIR/coq.v
ln -s $HOL2DK_DIR/_CoqProject
```

Once HOL-Light files have been translated to Lambdapi files, it is possible
to translate Lambdapi files into [Coq](https://coq.inria.fr/) files
using the Coq export feature of Lambdapi.

If your Lambdapi files have been generated using `file.mk`, you can simply do:
```
make -j $jobs -f file.mk v # to generate Coq files
make -j $jobs -f file.mk vo # to check the generated Coq files
```

To indicate a specific `lambdapi` command, do:
```
make -j $jobs -f file.mk LAMBAPI=$lambdapi v # to generate Coq files
```

Otherwise, you need to translate Lambdapi files one by one by hand or
using a script:
```
lambdapi export -o stt_coq --encoding $HOL2DK_DIR/encoding.lp --erasing $HOL2DK_DIR/erasing.lp --renaming $HOL2DK_DIR/renaming.lp --requiring coq.v file.lp | sed -e 's/hol-light\.//g' > file.v
```

You can then check the generated Coq files as follows:
```
echo coq.v theory_hol.v file*.v > _CoqProject
coq_makefile -f _CoqProject -o Makefile.coq
make -j $jobs -f Makefile.coq
```

Results
-------

Dumping of `hol.ml`:
  * checking time without proof dumping: 1m14s
  * checking time with proof dumping: 1m44s (+40%)
  * dumped files size: 3 Go
  * number of named theorems: 2842
  * number of proof steps: 8.5 M (8% unused)
  * simplification time: 1m18s
  * number of simplifications: 462 K (5%)
  * unused proof steps after simplification: 19% 

| rule       |  % |
|:-----------|---:|
| `refl`       | 32 |
| `eqmp`       | 14 |
| `comb`       | 12 |
| `term_subst` | 9 |
| `trans`      |  5 |
| `type_subst` |  3 |
| `beta`       |  4 |
| `abs`        |  2 |
| `spec`       |  2 |

Results on a machine with 32 processors i9-13950HX and 64 Go RAM:

Multi-threaded translation to Lambdapi with `dg 100`:
  * hol2dk dg: 14s
  * lp files generation time: 36s
  * lp files size: 1.6 Go
  * type abbrevs: 1.1 Mo
  * term abbrevs: 652 Mo (40%)
  * verification by lambdapi: fails (too big for lambdapi)
  * translation to Coq: 28s 1.5 Go
  * verification by Coq: 1h52

Multi-threaded translation to Dedukti with `dg 100`:
  * dk file generation time: 1m7s
  * dk file size: 2.3 Go
  * type abbrevs: 1.2 Mo
  * term abbrevs: 737 Mo (32%)
  * dkcheck: 5m23s
  * kocheck: 5m54s

Single-threaded translation to Lambdapi (data of 12 March 2023):
  * lp files generation time: 12m8s
  * lp files size: 2.5 Go
  * type abbreviations: 460 Ko
  * term abbreviations: 787 Mo (31%)

Single-threaded translation to Dedukti (data of 12 March 2023):
  * dk files generation time: 22m37s
  * dk files size: 3.6 Go
  * type abbreviations: 524 Ko
  * term abbreviations: 820 Mo (23%)

Results for `hol.ml` up to `arith.ml` (by commenting from `loads "wf.ml"` to the end) with `dg 7`:
  * proof dumping time: 11s 77 Mo (448 named theorems)
  * number of proof steps: 302 K (9% unused)
  * prf simplification: 2s
  * unused proofs after simplification: 20%
  * dk file generation: 2s 55 Mo
  * checking time with dk check: 7s
  * lp file generation: 1s 38 Mo
  * checking time with lambdapi: 61s
  * translation to Coq: 1s 36 Mo
  * checking time for Coq 8.18.0: 2m4s

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

Results on `hol.ml` upto `arith.ml` (by commenting from `loads "wf.ml"` to the end):
  * ocaml proof dumping: 13.2s
  * number of proof steps: 564351
  * proof dumping: 1.4s 157 Mo
  * dk file generation: 45s 153 Mo
  * checking time with dk check: 26s
  * checking time with kocheck -j 7: 22s
  * lp file generation: 29s 107 Mo
  * checking time with lambdapi: 2m49s

Results on `hol.ml`:
  * ocaml cheking without proof dumping: 1m14s
  * ocaml proof dumping: 2m9s (+74%)
  * proof size file: 5.5 Go
  * number of proof steps: 14.3 M

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
