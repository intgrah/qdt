(lang dune 3.20)

(name qdt)

(generate_opam_files true)

(source
 (github intgrah/qdt))

(authors "Jeremy Chen <git@sl.intgrah.com>")

(license LICENSE)

(package
 (name qdt)
 (synopsis "Query-based Dependent Type Elaborator")
 (description "Query-based Dependent Type Elaborator")
 (depends
  ocaml
  incremental
  (alcotest :with-test)
  (bisect_ppx :with-test)))
