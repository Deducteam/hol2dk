(lang dune 3.7)

(name hol2dk)

(generate_opam_files true)

(source
 (github Deducteam/hol2dk))

(authors "Frédéric Blanqui")

(maintainers "Frédéric Blanqui")

(license CeCILL-2.1)

(documentation https://github.com/Deducteam/hol2dk/blob/master/README.md)

(package
 (name hol2dk)
 (synopsis "HOL-Light to Dedukti/Lambdapi translator")
 (description "HOL-Light to Dedukti/Lambdapi translator")
 (depends
  ocaml
  dune
 )
)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
