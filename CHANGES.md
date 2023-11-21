All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## Unreleased

### Added

- add command dump-use for dumping a file without including "hol.ml"

### Modified

- rename mk-part command into mk
- the dump command now includes "hol.ml"
- do not print ocaml warnings while dumping proofs
- do not export unused proofs (about 7%)

### Fixed

- README.md
- output of hol2dk axm
- output of hol2dk mk

## 0.0.0 (2023-11-08)

First release.
