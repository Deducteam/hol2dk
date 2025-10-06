(lang dune 3.7)

(name hol2dk)

(generate_opam_files true)

(source (github Deducteam/hol2dk))

(documentation "https://github.com/Deducteam/hol2dk/blob/master/README.md")

(authors "Frédéric Blanqui")

(maintainers "Frédéric Blanqui")

(license CeCILL-2.1)

(package
 (name hol2dk)
 (synopsis "HOL-Light to Dedukti/Lambdapi and Rocq translator")
 (description "HOL-Light to Dedukti/Lambdapi and Rocq translator")
 (depends
  dune
  (ocaml (>= 4.13))
  (hol_light (= 3.0.0))
  (lambdapi (= 3.0.0))
)
)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
