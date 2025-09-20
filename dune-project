(lang dune 3.20)

(name moo)

(generate_opam_files true)

(using menhir 3.0)

(source
 (github s-kybound/moo))

(authors "Kyriel Abad <abadkyriel@gmail.com>")

(package
 (name moo)
 (synopsis "A language for a minimal mu mu-tilde dual calculus")
 (description "A language to investigate the minimal language needed to support ergonomic sequent-calculus based programming")
 (depends ocaml)
 (tags
  ("duality" "continuations" "interpreter")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
