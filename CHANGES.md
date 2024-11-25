All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## Unrelease

### Added

- alignment of the type of reals and basic functions on reals

## 2.0.0 (2024-04-23)

Big improvements in Lambdapi and Coq file generation time, and Coq checking time.

### Added

- hol2dk can now generate term abbreviations and proofs in several files
in parallel:
  * The option --max-size-abbrev allows to fix the maximum size for term abbreviations files.
  * The option --max-size-proof allows to fix the maximum size for proof files.
- optimization of lp file dependencies in generated lp files.
- generation of Makefile lpo dependencies at the same time as lp files.
- Makefile: lpo and vo dependencies are recomputed automatically.

### Changed

- FILES_WITH_SHARING renamed into BIG_FILES and not added by add-links anymore
- command dump[-simp]-use renamed into dump[-simp]-before-hol
- for each theorem, two files are generated: one with the proof, and one declaring the theorem as an axiom

## 1.0.0 (2024-02-25)

### Added

- add-links script
- command rewrite to simplify prf files
- command purge to compute useless theorems
  these two commands greatly reduce the size of generated proofs
- command simp is equivalent to rewrite and purge
- command dump-simp is equivalent to dump, pos, use and simp
- allow simultaneous dumping
- alignments of the types option, Sum, list, char, nadd
- command split to generate a pos/use/sti/nbp file for each named theorem
  (an sti file contains the starting index of the corresponding proof)
- command theorem to generate the lp files corresponding to a named theorem
- Makefile to generate and check lp and coq files generated with split
- command size to get statistics on the size of terms
- option --print-stats to print statistics on hash tables at exit
- use hash tables instead of maps to build abbreviations maps
- use sharing when building canonical types and terms
- add option --use-sharing for using sharing in lp output when defining term abbreviations
- command nbp to get the number of proof steps
- commands patch, unpatch and link to call the corresponding scripts
- command env to print $HOL2DK_DIR and $HOLLIGHT_DIR

### Modified

- identifier renamings
- merged the command dg in the command mk
- fusion.ml: do not generate new theorems for empty instantiations

### Fixed

- valid dedukti and lambdapi identifiers

## 0.0.1 (2023-11-22)

### Added

- add command dump-use for dumping a file without including "hol.ml"

### Modified

- rename mk-part command into mk
- the dump command now includes "hol.ml"
- do not print ocaml warnings while dumping proofs
- do not export unused proofs (about 7%)
- make hol2dk stat give the number of unused proofs

### Fixed

- README.md
- output of hol2dk axm
- output of hol2dk mk

## 0.0.0 (2023-11-08)

First release.
