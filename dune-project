(lang dune 2.9)
(name predicativize)
(generate_opam_files true)
(source (github Deducteam/predicativize))
(authors "thiago.felicissimo@inria.fr")
(maintainers "thiago.felicissimo@inria.fr")
(license CECILL-2.1)

(package
 (name predicativize)
 (synopsis "A tool for sharing proofs with predicative systems")
 (description "A tool for sharing proofs with predicative systems")
 (depends
  (ocaml (>= 4.10))
  (dedukti (= 2.7))
 )
)
