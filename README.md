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

If you don't have HOL-Light already installed, you can install it in
the current directory using the following script:

```
git clone --depth 1 -b master https://github.com/jrh13/hol-light
make -C hol-light
```

**Requirements:**
- libipc-system-simple-perl
- libstring-shellquote
- ocaml 4.14.1
- ocamlfind
- num
- camlp5.8.00.03

```
sudo apt-get install -y libipc-system-simple-perl libstring-shellquote
-perl
opam install ocamlfind num camlp5
```

To see other potential working ocaml-camlp5 pairs, see https://github.com/jrh13/hol-light/pull/71 .

Patching HOL-Light
------------------

```
./patch-hol-light $hol-light-dir
```

This script slightly modifies the file fusion.ml to dump proofs in the
file `proofs.dump`.

Usage
-----

```
cd $hol-light-dir
$hol2dk-dir/dump-proofs file.ml # a prefix of hol.ml

cd $hol2dk-dir
dune exec -- hol2dk $hol-light-dir/proofs.dump file.dk
dune exec -- hol2dk $hol-light-dir/proofs.dump file.lp
```

Checking the generated dk/lp files
----------------------------------

**Requirements:**
- dedukti 2.7
- lambdapi 2.3

```
opem install dedukti lambdapi
```

To check the generated dk file with [dkcheck](https://github.com/Deducteam/Dedukti/), write:
```
dk check myfile.dk
```

To check the generated dk file with the current version of
[kocheck](https://github.com/01mf02/kontroli-rs), you first need to
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
versions, it is convenient to use different switches in each directory:

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

Impact of proof recording on hol-light:

for checking hol.ml:
- without proof recording: 1m18s
-    with proof recording: 1m32s (+18%)
- proof dumping: 2m30s 5.5Go

On `hol.ml` until `arith.ml` (by commenting from `loads "wf.ml"` to the end):
- ocaml proof checking: 12.5s
- ocaml proof checking and recording: 13.2s
- proof dumping: 1.4s 157 Mo
- dk file generation: 45s 153 Mo
- checking time with dk check: 26s
- checking time with kocheck -j 7: 22s
- lp file generation: 29s 107 Mo
- checking time with lambdapi: 2m49s

Implementation
--------------

HOL-Light proof recording follows
[ProofTrace](https://github.com/fblanqui/hol-light/tree/master/ProofTrace)
developed by Stanislas Polu in 2019.
