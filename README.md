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
as well, but it takes a much longer time for Coq and Lambdapi to check
the generated files (16 minutes for Coq for `hol.ml`).

For bigger libraries like `Multivariate`, it takes more time,
especially for Coq. For instance, the `Multivariate` library up to
`topology.ml` can be translated to Lambdapi in 18 minutes, then to Coq
in 18 more minutes, and the verification of the generated files by Coq
takes 8 hours.

While it is possible to translate any HOL-Light
proof to Coq, the translated theorems may not be directly usable by
Coq users because not all HOL-Light types and functions are aligned
with those of the Coq standard library yet. Currently, we only aligned
the types of natural numbers and lists, and some functions on them in
the file
[coq.v](https://github.com/Deducteam/hol2dk/blob/main/coq.v). We
gathered the resulting theorems in the Opam package
[coq-hol-light](https://github.com/Deducteam/coq-hol-light) available
in the Coq Opam repository [released](https://github.com/coq/opam). We
plan to add more mappings, especially on real numbers.

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
- hol-light >= af186e9f3c685f5acab16097b05717c10ebb030d (28/01/23) <= c153f40da8deb3bcc7aaef39126ad15e4713e68c (20/03/24)
- libipc-system-simple-perl
- libstring-shellquote
- ocaml 4.14.1
- camlp5 8.02.01
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

The command `purge` compute in `file.use` all the theorems that do not need to be translated. For instance, in the HOL-Light base library `hol.ml`, 60% of proof steps are useless after simplication.

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
in parallel using `make`: `split` and `mk`. Currently, only `mk`
allows to generate dk files, but `split` generate lp and coq files
that are faster to check.

Remark: for not cluttering HOL-Light sources with generated files, we suggest to proceed as follows. For instance, for generating the proofs for `hol.ml`:
```
cd $HOLLIGHT_DIR
hol2dk dump-simp-use hol.ml
mkdir -p ~/output-hol2dk/hol
cd ~/output-hol2dk/hol
hol2dk link hol
```
This will add links to files needed to generate, translate and check proofs.

**By generating a lp file for each named theorem: command `split`**

```
hol2dk split file
```
generates file.thp and files t.sti, t.nbp, t.pos and t.use for each named theorem t.

After `hol2dk link`, you can use `make -j$jobs TARGET` to translate and check files in parallel, where `TARGET` is either:
- `split` to do `hol2dk split`
- `lp` to generate lp files
- `v` to translate lp files to Coq
- `lpo` to check lp files
- `vo` to check Coq files

The order targets are done important: `split` must be done first, then
`lp`, etc.

To speed up lp file generation for some theorems with very big proofs, you can write in a file called `BIG_FILES` a list of theorem names (lines starting with `#` are ignored).

**By splitting proofs in several parts: command `mk`**

```
hol2dk mk $nb_parts file
```
generates `file.dg` and `file.mk`.

Then generate and check `file.dk` with:

```
make -f file.mk -j$jobs dk
```

And `file.lp` with:

```
make -f file.mk -j$jobs lp
```

Checking the generated dk file
------------------------------

**Requirement:** dedukti >= 2.7, [kocheck](https://github.com/01mf02/kontroli-rs), or lambdapi >= 2.3.0

If you didn't use `hol2dk link`, add a link to the dk file defining the logic of HOL-Light:
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
kocheck -j7 file-for-kocheck.dk
```

Checking the generated lp files
-------------------------------

**Requirement:** lambdapi >= 2.3.0 for single-threaded generated files, lambdapi master branch for multi-threaded generated files

If you didn't use `hol2dk link`, add links to the following files:
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

If you didn't use `hol2dk link`, add links to the following files:
```
ln -s $HOL2DK_DIR/coq.v
ln -s $HOL2DK_DIR/_CoqProject
```

Once HOL-Light files have been translated to Lambdapi files, it is possible
to translate the obtained Lambdapi files into [Coq](https://coq.inria.fr/) files
using the Coq [export](https://lambdapi.readthedocs.io/en/latest/options.html#export) feature of Lambdapi.

If the lp files have been generated using `split`, simply do:
```
make -j$jobs v
```

If the lp files have been generated using `mk`, simply do:
```
make -f file.mk -j$jobs v
```

Otherwise, you need to translate Lambdapi files one by one by hand or
by using a script:
```
lambdapi export -o stt_coq --encoding $HOL2DK_DIR/encoding.lp --erasing $HOL2DK_DIR/erasing.lp --renaming $HOL2DK_DIR/renaming.lp --requiring coq.v file.lp | sed -e 's/hol-light\.//g' > file.v
```

You can then check the generated Coq files as follows.
If the lp files have been generated with `split`, simply do:
```
make -j$jobs vo
```
If the lp files have been generated using `mk`, simply do:
```
make -f file.mk -j$jobs vo
```

In case of big libraries like Multivariate, the memory consumption can be very high. To reduce it, we provide a command
```
make -j$jobs spec
```
which modifies Coq files as follows. For each file `theorem.v` containing the proof of a theorem, we generate a file `theorem_spec.v` containing the statement of the theorem as axiom. Then, in every file using that theorem, we replace `Require theorem` by `Require theorem_spec`.

To undo the `spec` command, simply do:
```
make -j$jobs unspec
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
- sum type constructor
- option type constructor
- type of lists
- functions on lists

The part of HOL-Light that is aligned with Coq is gathered in the package
[coq-hol-light](https://github.com/Deducteam/coq-hol-light) available
in the Coq Opam repository [released](https://github.com/coq/opam).

Performance on 15/04/24
-----------------------

On a machine with 32 processors i9-13950HX and 64G RAM:

| HOL-Light file       | dump-simp | dump size | proof steps | nb theorems | make -j32 lp | make -j32 v | v files size | make -j32 vo |
|----------------------|-----------|-----------|-------------|-------------|--------------|-------------|--------------|--------------|
| hol.ml               | 2m36s     | 3 Go      | 8 M         | 5679        | 36s          | 25s         | 0.4 Go       | 16m22s       |
| Multivariate/make.ml | 1h55m     | 52 Go     | 89 M        | 18866       | 18m11s       | 18m43s      | 2.3 Go       | 8h (*)       |

(*) make -j32 vo; make -j8 vo

Getting statistics on proofs
----------------------------

It is possible to get statistics on proofs by using some commands. For instance, the command `stat` tells how many times each deduction rule is used:

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
