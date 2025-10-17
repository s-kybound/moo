# moo: a dual language to explore the dual mu mu-tilde calculus

moo is a tiny, dual, cut‑centric calculus meant to answer:

- What is the smallest set of data connectives, together with μ/μ̃ and cut, that regains the expressiveness of the λ‑calculus—first simply (untyped), then with types (STLC), and finally with impredicative polymorphism (System F)?

- Can we do this while omitting λ‑abstraction as a primitive and relying instead on the dual control binders μ and μ̃?



We first experiment with an untyped language, followed by the equivalent of the STLC for this calculus, followed by a 
full System F equivalent for mu mu-tilde calculus.

## Dependencies
- cmdliner
- dune-build-info
- linenoise
- menhir

## Usage

Install with `dune build` + `dune install`

`moo --help` will display all possible options, namely
- `moo repl` launches the REPL
- `moo <PROGRAM>` or `moo run <PROGRAM>` will run a program to completion
