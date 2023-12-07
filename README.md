Export HOL-Light proofs to Dedukti, Lambdapi and Coq
====================================================

This project provides a tool to translate [HOL-Light](https://github.com/jrh13/hol-light) proofs to [Dedukti](https://github.com/Deducteam/Dedukti/), [Lambdapi](https://github.com/Deducteam/lambdapi) and [Coq](https://coq.inria.fr/).

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

Results
-------

The HOL-Light base library `hol.ml` and the library `Logic/make.ml`
formalizing the metatheory of first-order logic can be exported and
translated to Dedukti, Lambdapi and Coq in a few minutes. However, it
may take hours for Coq and require too much memory for Lambdapi to
check the translated files. Bigger libraries like
`Multivariate/make.ml` requires too much memory for the moment. But we
will fix this soon.

Moreover, while it is possible to translate any HOL-Light proof to
Coq, the translated theorem may not be directly usable by Coq users
because HOL-Light types and functions may not be aligned with those of
the Coq standard library yet. Currently, only the type of natural
numbers and various functions on natural numbers have been aligned. We
gathered the obtained 448 lemmas in the package
[coq-hol-light](https://github.com/Deducteam/coq-hol-light) available
in the Coq Opam repository [released](https://github.com/coq/opam).

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
hol2dk dump-use-simp file.ml
```
where `file.ml` should at least contain the contents of `hol.ml` until the line `loads "fusion.ml";;`.

The command `dump-simp` (and similarly for `dump-use-simp`) are actually the sequential composition of various lower level commands: `dump`, `pos`, `use`, `rewrite` and `purge`:

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
cd $HOLLIGHT_DIR
hol2dk dump-use-simp hol.ml
cd $HOME
mkdir output-hol2dk
cd output-hol2dk
$HOL2DK_DIR/add-links hol
cd hol
hol2dk dg 100 hol
hol2dk mk hol
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

If the Lambdapi files have been generated using `file.mk`, you can simply do:
```
make -j $jobs -f file.mk v # to generate Coq files
make -j $jobs -f file.mk vo # to check the generated Coq files
```

To indicate a specific `lambdapi` command, do:
```
make -j $jobs -f file.mk LAMBAPI=$lambdapi v
```

Otherwise, you need to translate Lambdapi files one by one by hand or
by using a script:
```
lambdapi export -o stt_coq --encoding $HOL2DK_DIR/encoding.lp --erasing $HOL2DK_DIR/erasing.lp --renaming $HOL2DK_DIR/renaming.lp --requiring coq.v file.lp | sed -e 's/hol-light\.//g' > file.v
```

You can then check the generated Coq files as follows:
```
echo coq.v theory_hol.v file*.v > _CoqProject
coq_makefile -f _CoqProject -o Makefile.coq
make -j $jobs -f Makefile.coq
```

Performance
-----------

Performance on a machine with 32 processors i9-13950HX and 64 Go RAM:

Translation of `Logic/make.ml` with `dg 32` (includes `Library/analysis`):
  * dump-simp 11m42s 10 Go 21.2 M steps (83% unused including hol.ml) +1729 named theorems
  * dk 1m13s dko 4m15s lp 42s v 12s vo 1h11ms
  
Translation of `hol.ml` with `dg 100`:
  * checking time without proof dumping: 1m14s
  * checking time with proof dumping: 1m44s (+40%)
  * dumped files size: 3 Go
  * number of named theorems: 2842
  * number of proof steps: 8.5 M (8% unused)
  * simplification time: 1m22s
  * number of simplifications: 1.2 M (14%)
  * unused proof steps after simplification: 29%
  * purge time: 11s
  * unused proof steps after purge: 60%

| rule         |  % |
|:-------------|---:|
| `comb`       | 20 |
| `term_subst` | 17 |
| `refl`       | 16 |
| `eqmp`       | 11 |
| `trans`      |  9 |
| `conjunct1`  |  5 |
| `abs`        |  3 |
| `beta`       |  3 |
| `mp`         |  3 |
| `sym`        |  2 |
| `deduct`     |  2 |
| `type_subst` |  2 |
| `assume`     |  1 |
| `conjunct2`  |  1 |
| `disch`      |  1 |
| `spec`       |  1 |
| `disj_cases` |  1 |
| `conj`       |  1 |

Multi-threaded translation to Lambdapi with `dg 100`:
  * hol2dk dg: 14s
  * lp files generation time: 31s
  * lp files size: 1.1 Go
  * type abbrevs: 796 Ko
  * term abbrevs: 583 Mo (53%)
  * verification by lambdapi: fails (too big for lambdapi)
  * translation to Coq: 24s 1 Go
  * verification by Coq: 64m13s

Multi-threaded translation to Dedukti with `dg 100`:
  * dk file generation time: 49s
  * dk file size: 1.5 Go
  * type abbrevs: 876 Ko
  * term abbrevs: 660 Mo (44%)
  * dkcheck: 3m31s
  * kocheck: 5m54s

Single-threaded translation to Lambdapi:
  * lp files generation time: 4m49s
  * lp files size: 1.1 Go
  * type abbreviations: 308 Ko
  * term abbreviations: 525 Mo (48%)

Single-threaded translation to Dedukti:
  * dk files generation time: 7m12s
  * dk files size: 1.4 Go
  * type abbreviations: 348 Ko
  * term abbreviations: 590 Mo (42%)

Translation of `arith.ml` with `dg 7`:
  * proof dumping time: 11s 77 Mo 448 named theorems
  * number of proof steps: 302 K (9% unused)
  * prf simplification: 2s
  * unused proofs after simplification: 31%
  * unused proofs after purge: 66%
  * dk file generation: 1s 29 Mo
  * checking time with dk check: 4s
  * lp file generation: 1s 21 Mo
  * checking time with lambdapi: 31s
  * translation to Coq: 1s 20 Mo
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
