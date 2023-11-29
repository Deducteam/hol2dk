All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## Unreleased

### Added

- add-links script
- command rewrite to simplify prf files
- command purge to compute useless theorems
  these two commands greatly reduce the size of generated proofs
- command simp is equivalent to rewrite and purge
- command dump-and-simp is equivalent to dump, pos, use and simp

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
