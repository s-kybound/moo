(lang dune 3.20)

(name pluto-charon)

(generate_opam_files true)

(source
 (github s-kybound/pluto-charon))

(authors "Kyriel Abad <abadkyriel@gmail.com>")

(package
 (name pluto-charon)
 (synopsis "A language for a minimal mu mu-tilde dual calculus")
 (description "A language to investigate the minimal language needed to support ergonomic sequent-calculus based programming")
 (depends ocaml)
 (tags
  ("duality" "continuations" "interpreter")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
