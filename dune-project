(lang dune 3.7)

(name hol2dk)

(generate_opam_files true)

(source (github Deducteam/hol2dk))

(documentation "https://github.com/Deducteam/hol2dk/blob/master/README.md")

(authors "Frédéric Blanqui" "Anthony Bordg")

(maintainers "Frédéric Blanqui")

(license CeCILL-2.1)

(package
 (name hol2dk)
 (synopsis "HOL-Light to Dedukti/Lambdapi and Coq translator")
 (description "HOL-Light to Dedukti/Lambdapi and Coq translator")
 (depends
  (ocaml (>= 4.13))
  dune
 )
)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
