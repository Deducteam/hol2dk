Export to Dedukti and Lambdapi proof formats
============================================

The branch dk of this fork of HOL-Light provides functions for
exporting HOL-Light proofs in the
[Dedukti](https://github.com/Deducteam/Dedukti/) and
[Lambdapi](https://github.com/Deducteam/lambdapi) proof formats.

Dedukti is a proof format based on the λΠ-calculus modulo rewriting
(λ-calculus + simple types + dependent types + implicit type
equivalence modulo user-defined rewriting rules).

Lambdapi is a proof assistant based on the λΠ-calculus modulo
rewriting that can read and generate Dedukti proofs.

Requirements
------------

- tested with ocaml 4.02.3 and camlp5 6.17, and ocaml 4.14.1 and camlp5.8.00.03
- dedukti 2.7
- lambdapi 2.3
- ledit (optional, to ease the use of ocaml toplevel)

To see other potential working ocaml-camlp5 pairs, see https://github.com/jrh13/hol-light/pull/71 .

Installation
------------

Get the sources of hol-light:
```
git clone https://github.com/jrh13/hol-light.git
```

In the following, we assume that we are in the `hol-light` directory
created by the previous `git clone` command:
```
cd hol-light
```

To setup hol-light, do the first time you clone hol-light, or if you
change the version of ocaml or the version of camlp5:

```
make
```

Get the sources of the dk branch:
```
git remote add deducteam https://github.com/Deducteam/hol-light.git
fetch deducteam
git checkout deducteam/dk
```

Usage
-----

Run the OCaml toplevel:
```
ocaml
```

If you want to use ledit, write:
```
ledit -x -h ~/.ocaml_history ocaml
```

You can add an alias in your `~/.bashrc` to save time.

In the OCaml toplevel, first write:
```
#use "xprelude.ml";;
#use "hol.ml";;
(* load any other HOL-Light file here *)
#use "xlib.ml";;
```

Then, to export to Dedukti, write:
```
#use "xdk.ml";;
export_to_dk_file "myfile.dk" All;;
```

And, to export to Lambdapi, write:
```
#use "xlp.ml";;
export_to_lp_file "myfile" All;;
```

This will be generate 3 lp files:
- `myfile_types.lp` containing HOL-Light types
- `myfile_terms.lp` containing HOL-Light terms
- `myfile_proofs.lp` containing HOL-Light proofs

By the way, to get some statistics on proofs, simply do:
```
print_proof_stats();;
```

Getting some information on HOL-Light files and theorems
--------------------------------------------------------

The file `xnames.ml` provides also various functions to get information on HOL-Light files and theorems:
```
#use "xnames.ml";;
(* list of HOL-Light files *)
files;;
(* map giving the theorems proved in each file *)
update_map_file_thms();;
!map_file_thms;;
(* map giving the name of each named theorem number *)
update_map_thm_id_name();;
!map_thm_id_name;;
(* map giving the number of every named theorem *)
update_map_name_thm_id();;
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

Checking the generated dk/lp files
----------------------------------

To check the generated dk file with [dkcheck](https://github.com/Deducteam/Dedukti/), write:
```
dk check myfile.dk
```

To check the generated dk file with the current version of
[kocheck](https://github.com/01mf02/kontroli-rs), we first need to
slightly change the generated file:

```
sed -e 's/^injective /def /g' myfile.dk > myfile2.dk
kocheck -j 7 myfile2.dk
```

To check the generated lp file with [lambdapi](https://github.com/Deducteam/lambdapi), write:
```
lambdapi check --map-dir hol-light:. myfile.lp
```

or create a file `lambdapi.pkg`:
```
package_name = hol-light
root_path = hol-light
```

and simply write:

```
lambdapi check myfile.lp
```

Remark: In case hol-light and dkcheck/lambdapi do not use the same ocaml
versions, it is convenient to put generated files in a subdirectory
and tell opam to use different switches in each directory:

Xterm 1 (for HOL-Light):
```
cd $hol_light_directory
opam switch link 4.02.3
eval `opam env`
```

Xterm 2 (for checking dk/lp files):
```
cd $hol_light_directory
mkdir xport
cd xport
opam switch link 4.14.1
eval `opam env`
```

Then, you simply need to generate dk and lp files in the `xport/` directory.

Results
-------

Impact of proof recording on hol-light:

checking hol.ml
- without proof recording: 1m18s
-    with proof recording: 1m32s (+18%)

It slightly improves on the performances of ProofTrace which takes
1m54s (+46%).

On `hol.ml` until `arith.ml` (by commenting from `loads "wf.ml"` to the end):
- ocaml proof checking: 12.5s
- ocaml proof checking and recording: 13.2s
- dk file generation: 2m6s, 153 Mo
- checking time with dk check: 26s
- checking time with kocheck -j 7: 22s
- lp file generation: 1m8s, 107 Mo
- checking time with lambdapi: 2m49s

Implementation
--------------

For extracting proofs out of HOL-Light, the implementation reuses
parts of
[ProofTrace](https://github.com/fblanqui/hol-light/tree/master/ProofTrace)
developed by Stanislas Polu in 2019.

Modified HOL-Light files:
- `fusion.ml`: file defining the theorem and proof types

Added files:
- `xprelude.ml`: load the necessary modules and provides a few global references
- `xlib.ml`: functions on types and terms
- `xnames.ml`: compute the list of HOL-Light files and a map associating the list of theorems proved in each file (following ProofTrace/proofs.ml)
- `xdk.ml`: function exporting HOL-Light proofs to Dedukti
- `xlp.ml`: function exporting HOL-Light proofs to Lambdapi
