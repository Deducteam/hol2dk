Export HOL-Light proofs to Dedukti, Lambdapi and Coq
====================================================

This project provides several programs:
- a script `patch` to patch HOL-Light to dump proofs
- a script `unpatch` to unpatch HOL-Light
- a program `hol2dk` to generate Dedukti or Lambdapi files from dumped proofs

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

Installing HOL-Light
--------------------

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

If you don't have HOL-Light already installed, you can install it by
using the following commands:

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

Patching HOL-Light
------------------

```
$hol2dk-dir/patch $hol-light-dir
```

This script slightly modifies a few HOL-Light files in order to dump proofs:
- `fusion.ml`: the HOL-Light kernel file defining types, terms, theorems, proofs and proof rules
- `bool.ml`: HOL-Light file defining basic tactics corresponding to introduction and elimination rules of connectives

To unpatch HOL-Light, siimply do:
```
$hol2dk-dir/unpatch $hol-light-dir
```

Compiling and installing hol2dk
----------------

**Requirements:**
- ocaml >= 4.14.1
- dune >= 3.7

```
cd $hol2dk-dir
dune build && dune install
```
compiles and installs `hol2dk`.

Summary of hol2dk commands
-------

Get it by running `hol2dk` without arguments.

Dumping HOL-Light proofs
------------------------

```
cd $hol-light-dir
hol2dk dump file.ml
```

generates the files `file.sig`, `file.prf` and `file.thm`.

`file.ml` should at least require `hol.ml` until the line `loads
"fusion.ml";;`.

WARNING: it is important to run `hol2dk dump` in the HOL-Light directory so as to compute the list of named theorems properly.

Generating dk/lp files from dumped files
--------------------------------------

The base theory in which HOL-Light proofs are translated is described in the files [theory_hol.lp](https://github.com/Deducteam/hol2dk/blob/main/theory_hol.lp) and [theory_hol.dk](https://github.com/Deducteam/hol2dk/blob/main/theory_hol.dk).

You first need to generate `file.pos` with:
```
hol2dk pos file
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
hol2dk dg file
hol2dk mk $nb_proc file # number of processors you can run in parallel
```

You can then generate `file.dk` with:

```
make -j $jobs -f file.mk dk
```

And `file_part_$jobs.lp` with:

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

Translating HOL-Light files to Coq
----------------------------------

Requirement: lambdapi master branch

Once HOL-Light files have been translated to Lambdapi files, it is possible
to translate Lambdapi files into [Coq](https://coq.inria.fr/) files
using the Coq export feature of Lambdapi.

If your Lambdapi files have been generated using `file.mk`, you can simply do:
```
hol2dk mk $n file coq.v
make -j 7 -f file.mk v # to generate Coq files
make -j 7 -f file.mk vo # to check the generated Coq files
```
To indicate a specific `lambdapi` command, to:
```
make -j 7 -f file.mk LAMBAPI=$lambdapi v # to generate Coq files
```

Otherwise, you need to translate Lambdapi files one by one by hand or using a script:
```
lambdapi export -o stt_coq --encoding encoding.lp --erasing erasing.lp --renaming renaming.lp --requiring coq.v file.lp | sed -e 's/hol-light\.//g' > file.v
```

You can then check the generated Coq files as follows:
```
echo coq.v theory_hol.v file*.v > _CoqProject
coq_makefile -f _CoqProject > Makefile.coq
make -j 7 -f Makefile.coq
```

Results
-------

Dumping of `hol.ml`:
  * checking time without proof dumping: 1m20s
  * checking time with proof dumping: 1m51s (+39%)
  * dumped files size: 3.8 Go
  * number of proof steps: 11 M

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

Multi-threaded translation to Lambdapi:
  * lp files generation time: 4m38s with `mk 7`, 5m5s with `mk 22`
  * lp files size: 2.5 Go
  * type abbrevs: 600 Ko
  * term abbrevs: 700 Mo
  * Unfortunately, Lambdapi is too slow and takes too much memory to be able to check so big files on my laptop. It can however check some prefix of `hol.ml` (see below).
  
Multi-threaded translation to Dedukti:
  * dk file generation time: 9m19s with `mk 7`, 8m56s with `mk 21`
  * dk file size: 3.7 Go
  * type abbrevs: 652 Ko
  * term abbrevs: 731 Mo
  * kocheck can check it in 12m52s
  * dkcheck is unable to check the generated dk file on my laptop for lack of memory (I have only 32 Go RAM and the process is stopped after 11m16s)

Results for `hol.ml` up to `arith.ml` (by commenting from `loads "wf.ml"` to the end):
  * proof dumping time: 13s 100 Mo
  * number of proof steps: 405 K
  * dk file generation: 20s 96 Mo
  * checking time with dk check: 19s
  * checking time with kocheck -j 7: 14s
  * lp file generation: 15s 69 Mo (4s with `mk 7`)
  * checking time with lambdapi: 1m53s (2m with `mk 7`)
  * translation to Coq: 3s with `mk 15` and `j 7`
  * checking time for Coq 8.17.1: 5m16s with `mk 15` and `j 7`

Exporting pure Q0 proofs
------------------------

Hol2dk instruments basic HOL-Light tactics corresponding to
introduction and elimination rules of connectives to get smaller
proofs and proofs closer to natural deduction proofs. It is however
possible to generate full Q0 proofs by patching HOL-Light files as
follows:

```
cd $hol-light-dir
sed -i -e 's/.*Q0.*//' -e 's/START_ND*)//' -e 's/(*END_ND//' fusion.ml bool.ml
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

Source files
------------

Modified HOL-Light files:
- `lib.ml`: HOL-Light file providing functions on lists, etc. required by `fusion.ml`. A few lines are commented out so that it compiles with ocamlc.
- `fusion.ml`: HOL-Light kernel file defining types, terms, theorems, proofs and elementary proof rules.
- `bool.ml`: HOL-Light file defining basic tactics corresponding to introduction and elimination rules of connectives.

The files `fusion.ml` and `bool.ml` contain special comments that are removed to patch hol-light.

Additional files required for `hol2dk`:
- `main.ml`: main program of Hol2dk.
- `xprelude.ml`: file providing a few basic definitions.
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
[ProofTrace](https://github.com/fblanqui/hol-light/tree/master/ProofTrace)
developed by Stanislas Polu in 2019.
