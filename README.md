Export HOL-Light proofs to Dedukti and Lambdapi
===============================================

This project provides several things:
- a script `patch-hol-light` to patch HOL-Light to dump proofs
- a script `unpatch-hol-light` to unpatch HOL-Light
- a script `dump-proofs` to dump proofs
- a compiled OCaml program `hol2dk` to generate Dedukti or Lambdapi files from dumped files

[HOL-Light](https://github.com/jrh13/hol-light) is proof assistant
based on higher-order logic, aka simple type theory.

[Dedukti](https://github.com/Deducteam/Dedukti/) is a proof format
based on the λΠ-calculus modulo rewriting (λ-calculus + simple types +
dependent types + implicit type equivalence modulo user-defined
rewriting rules).

[Lambdapi](https://github.com/Deducteam/lambdapi) is a proof assistant
based on the λΠ-calculus modulo rewriting that can read and generate
Dedukti proofs.

Installing HOL-Light
--------------------

**Requirements:**
- libipc-system-simple-perl
- libstring-shellquote
- ocaml 4.14.1
- camlp5.8.00.03
- ocamlfind
- num

Find other potential working ocaml-camlp5 pairs on
https://github.com/jrh13/hol-light/pull/71 .

If you don't have HOL-Light already installed, you can install it in
the current directory using the following commands:

```
sudo apt-get install -y libipc-system-simple-perl libstring-shellquote
-perl
opam install ocamlfind num camlp5
git clone --depth 1 -b master https://github.com/jrh13/hol-light
make -C hol-light
```

Patching HOL-Light
------------------

```
./patch-hol-light $hol-light-dir
```

This script slightly modifies a few HOL-Light files in order to dump proofs:
- `fusion.ml`: the HOL-Light kernel file defining types, terms, theorems, proofs and proof rules
- `bool.ml`: HOL-Light file defining basic tactics corresponding to introduction and elimination rules of connectives

Dumping HOL-Light proofs
------------------------

```
cd $hol-light-dir
$hol2dk-dir/dump-proofs file.ml
```

generates two files: `file.sig` and `file.prf`.

`file.ml` should at least include `hol.ml` until the line `loads
"fusion.ml";;`.

Compiling and installing hol2dk
----------------

**Requirements:**
- ocaml >= 4.14.1
- dune >= 3.7

```
dune build
dune install
```
compiles and installs `hol2dk`.

Get statistics on proofs
------------------------

```
hol2dk file.lp --stats
```

Generating dk/lp files from dumped files
--------------------------------------

You first need to generate `file.pos` with:
```
hol2dk file.dk --pos
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

You first generate `file.mk` with:
```
hol2dk file.dk --part $jobs # number of processors you can run in parallel
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

**Requirement:** lambdapi 2.3, dedukti 2.7 or [kocheck](https://github.com/01mf02/kontroli-rs)

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

**Requirement:** lambdapi 2.3

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

Multi-threaded translation to Lambdapi (with `--part 7`):
  * lp files generation time: 4m38s
  * lp files size: 2.5 Go
  * type abbrevs: 600 Ko
  * term abbrevs: 700 Mo
  * Unfortunately, Lambdapi is too slow and takes too much memory to be able to check so big files on my laptop. It can however check some prefix of `hol.ml` (see below).
  
Multi-threaded translation to Dedukti (with `--part 7`):
  * dk file generation time: 9m19s
  * dk file size: 3.7 Go
  * type abbrevs: 652 Ko
  * term abbrevs: 731 Mo
  * kocheck can check it in 12m52s
  * dkcheck is unable to check the generated dk file on my laptop for lack of memory (I have only 32 Go RAM and the process is stopped after 11m16s)

Results for `arith.ml` (i.e. `hol.ml` until `arith.ml`):
  * proof dumping time: 13s 101 Mo
  * number of proof steps: 409 K
  * dk files generation: 26s 99 Mo
  * checking time with dk check: 21s
  * checking time with kocheck -j 7: 14s
  * lp files generation: 17s 69 Mo
  * checking time with lambdapi: 1m54s

Getting information on HOL-Light files and theorems
---------------------------------------------------

In `$hol-light-dir`, run `ocaml` and type:

```
#use "topfind";;
#require "camlp5";;
#load "camlp5o.cma";;
#load "str.cma";;
#use "xprelude.ml";;
#use "hol.ml";;
(* #use any other HOL-Light file here *)

#use "xlib.ml";;
#use "xnames.ml";;

(* list of HOL-Light files *)
files;;

(* map giving the names of theorems proved in each file *)
update_map_file_thms();;
!map_file_thms;;

(* map giving the name of each named theorem number *)
update_map_thm_id_name();;
!map_thm_id_name;;

(* map giving the number of every named theorem *)
update_map_thm_name_id();;
!map_name_thm_id;;

(* function returning the number of a theorem name *)
thm_id;;

(* dependency graph of HOL-Light files *)
update_map_file_deps();;
!map_file_deps;;

(* function outputing the dependency graph in Makefile syntax *)
print_map_file_deps_to;;

(* function giving the declared dependencies of a file *)
deps;;

(* function giving the list of all files a file depends on*)
trans_deps;;
```

Exporting pure Q0 proofs
-------------------

Hol2dk instruments basic HOL-Light tactics corresponding to
introduction and elimination rules of connectives to get smaller
proofs and proofs closer to natural deduction proofs. It is however
possible to generate full Q0 proofs by patching HOL-Light files as
follows:

```
cd $hol-light-dir
sed -i -e 's/.*Q0.*//' -e 's/START_ND*)//' -e 's/(*END_ND//' fusion.ml bool.ml
```

Results on `hol.ml` until `arith.ml` (by commenting from `loads "wf.ml"` to the end):
- ocaml proof dumping: 13.2s
- number of proof steps: 564351
- proof dumping: 1.4s 157 Mo
- dk file generation: 45s 153 Mo
- checking time with dk check: 26s
- checking time with kocheck -j 7: 22s
- lp file generation: 29s 107 Mo
- checking time with lambdapi: 2m49s

Source files
------------

Modified HOL-Light files:
- `lib.ml`: HOL-Light file providing functions on lists, etc. required by `fusion.ml`. A few lines are commented out so that it compiles with ocamlc.
- `fusion.ml`: HOL-Light kernel file defining types, terms, theorems, proofs and elementary proof rules.
- `bool.ml`: HOL-Light file defining basic tactics corresponding to introduction and elimination rules of connectives.

The files `fusion.ml` and `bool.ml` contains special comments that are removed to patch hol-light.

Additional files required for `hol2dk`:
- `main.ml`: main program of Hol2dk.
- `xprelude.ml`: file providing a few basic definitions.
- `xproof.ml`: functions for accessing proofs.
- `xlp.ml`: translation to Lambdapi of types, terms and proofs.
- `xdk.ml`: translation to Dedukti of types, terms and proofs.
- `xci.ml`: slightly truncated version of the HOL-Light file `hol.ml` used for testing

Note that all these files can be used in the OCaml toplevel as well by removing the `open` instructions and by adding `unset_jrh_lexer;;` and `set_jrh_lexer;;` at the beginning and at the end of the file.

Other files that can be used in the OCaml toplevel:
- `xnames.ml`: to get information on file dependencies and named theorems

Thanks
------

HOL-Light proof recording follows
[ProofTrace](https://github.com/fblanqui/hol-light/tree/master/ProofTrace)
developed by Stanislas Polu in 2019.
