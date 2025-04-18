(lang dune 3.18)

(name folderol)

(generate_opam_files true)

(source
 (github IntGrah/folderol))

(authors "IntGrah <git@sl.intgrah.com>")

(license LICENSE)

(package
 (name folderol)
 (synopsis "First-order logic theorem prover")
 (description
  "First-order logic theorem prover based on Lawrence Paulson's Standard ML implementation")
 (depends ocaml)
 (tags
  ("theorem" "prover" "logic")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
