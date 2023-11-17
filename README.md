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

```
git clone https://github.com/Deducteam/hol2dk.git
cd hol2dk
dune build && dune install
```

Setting the environment variable `$HOL2DK_DIR`
----------------------------------------------

For some commands to have access to files in hol2dk sources, you need
to set the following environment variable:

```
export HOL2DK_DIR=$hol2dk_dir
```

where `$hol2dk_dir` is the absolute path to the directory where the
hol2dk sources are.

Patching HOL-Light sources
--------------------------

```
cd $(HOL2DK_DIR)
./patch $(HOL_LIGHT_DIR)
```

where $(HOL_LIGHT_DIR) is the directory where are the sources of HOL-Light.

This script slightly modifies a few HOL-Light files in order to dump proofs:
- `fusion.ml`: the HOL-Light kernel file defining types, terms, theorems, proofs and proof rules
- `bool.ml`: HOL-Light file defining basic tactics corresponding to introduction and elimination rules of connectives
- `equal.ml`: HOL-Light file defining basic tactics on equality

The patch also adds a file `xnames.ml`.

Before applying the patch, a copy of these files is created in `fusion-bak.ml`, `bool-bak.ml`, etc.

To unpatch HOL-Light, simply do:
```
cd $(HOL2DK_DIR)
./unpatch -y $(HOL_LIGHT_DIR)
```

Summary of hol2dk commands
--------------------------

Get it by running `hol2dk` without arguments.

Dumping HOL-Light proofs
------------------------

```
cd $(HOL_LIGHT_DIR)
hol2dk dump file.ml
```

generates the files `file.sig`, `file.prf` and `file.thm`.

`file.ml` should at least require `hol.ml` until the line `loads
"fusion.ml";;`.

WARNING: it is important to run `hol2dk dump` in the HOL-Light directory so as to compute the list of named theorems properly.

Generating dk/lp files from dumped files
--------------------------------------

The base theory in which HOL-Light proofs are translated is described in the files [theory_hol.lp](https://github.com/Deducteam/hol2dk/blob/main/theory_hol.lp) and [theory_hol.dk](https://github.com/Deducteam/hol2dk/blob/main/theory_hol.dk).

You first need to generate `file.pos` and `file.use` with:
```
hol2dk pos file
hol2dk use file
```

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

You first generate `file.dg` and `file.mk` with:
```
hol2dk dg $nb_parts file
hol2dk mk-part file
```
where `$nb_parts` is the number of files in which you want to split the proofs.

You add links to hol2dk files:
```
ln -s $HOL2DK_DIR/theory_hol.dk
ln -s $HOL2DK_DIR/theory_hol.lp
ln -s $HOL2DK_DIR/lambdapi.pkg
ln -s $HOL2DK_DIR/coq.v
ln -s $HOL2DK_DIR/_CoqProject
```

You can then generate `file.dk` with:

```
make -j $jobs -f file.mk dk
```

And `file.lp` with:

```
make -j $jobs -f file.mk lp
```

Checking the generated dk file
------------------------------

**Requirement:** lambdapi >= 2.3.0, dedukti >= 2.7 or [kocheck](https://github.com/01mf02/kontroli-rs)

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

To check the generated lp files with
[lambdapi](https://github.com/Deducteam/lambdapi), do:

```
lambdapi check --map-dir hol-light:. file.lp
```

or create a file `lambdapi.pkg`:
```
package_name = hol-light
root_path = hol-light
```

and simply do:

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

Requirement: lambdapi master branch

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
lambdapi export -o stt_coq --encoding $(HOL2DK_DIR)/encoding.lp --erasing $(HOL2DK_DIR)/erasing.lp --renaming $(HOL2DK_DIR)/renaming.lp --requiring $(HOL2DK_DIR)/coq.v file.lp | sed -e 's/hol-light\.//g' > file.v
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
  * dumped files size: 3.1 Go
  * number of proof steps: 8.9 M (2834 theorems)

| rule       |  % |
|:-----------|---:|
| refl       | 29 |
| eqmp       | 19 |
| comb       | 17 |
| term_subst | 12 |
| trans      |  6 |
| type_subst |  3 |
| beta       |  3 |
| abs        |  2 |
| spec       |  2 |

Single-threaded translation to Lambdapi:
  * lp files generation time: 12m8s
  * lp files size: 2.5 Go
  * type abbreviations: 460 Ko
  * term abbreviations: 787 Mo (31%)

Single-threaded translation to Dedukti:
  * dk files generation time: 22m37s
  * dk files size: 3.6 Go
  * type abbreviations: 524 Ko
  * term abbreviations: 820 Mo (23%)

Multi-threaded translation to Lambdapi with `mk 100` and `-j 28`:
  * hol2dk dg: 15s
  * lp files generation time: 1m5s
  * lp files size: 2.1 Go
  * type abbrevs: 1.3 Mo
  * term abbrevs: 681 Mo
  * verification by lambdapi with 64 Go RAM: 4h10
  * translation to Coq: 50s 1.9 Go
  * verification by Coq with 64 Go RAM: 6h

Multi-threaded translation to Dedukti with `mk 100`:
  * dk file generation time: 1m57s
  * dk file size: 3 Go
  * type abbrevs: 1.3 Mo
  * term abbrevs: 772 Mo
  * kocheck with 32 Go RAM: 12m52s
  * dkcheck with 64 Go RAM: 14m05s

Results for `hol.ml` up to `arith.ml` (by commenting from `loads "wf.ml"` to the end) with `mk 7` and `-j 7` :
  * proof dumping time: 12s 77 Mo
  * number of proof steps: 302 K
  * dk file generation: 6s 76 Mo
  * checking time with dk check: 13s
  * lp file generation: 4s 52 Mo
  * checking time with lambdapi: 1m22s (1m30s with `-c`)
  * translation to Coq: 2.8s 52 Mo
  * checking time for Coq 8.18.0: 4m34s

Exporting pure Q0 proofs
------------------------

Hol2dk instruments basic HOL-Light tactics corresponding to
introduction and elimination rules of connectives to get smaller
proofs and proofs closer to natural deduction proofs. It is however
possible to generate full Q0 proofs by doing after patching:

```
cd $(HOL_LIGHT_DIR)
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
