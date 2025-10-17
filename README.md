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

## What does the language look like?

```
{* encoding sums as products
 * a sum type is a negative pair of a and b continuations. *}
type (sum a b) = (& ~a ~b) ;;

{* encoding functions as products
 * a function type is a negative pair of A expression and B continuation *}
type (fun A B) = (& A ~B) ;;

{* see a function as a codata value responding to an observation
 * of a value and a context/continuation. 'ap represents the function call. *}
defp [inl : (fun A+ (sum A+ B+)+)+] 'ap =
  {* 'ap delivers the value v and the continuation, that expects
   * a sum type *}
  cosplit [v : A+] ['cont : (sum A+ B+)-] <- 'ap in
  {* given v, we create a codata type that will respond to cont, which contains 2 continuations
   * by supplying it only v *}
  cosplit ['a_cont : A-] _ <- 'cont in
  [v 'a_cont]

{* our test involves producing a sum type and casing on it! *}
let sum <- (letcc 'k -> [inl '(A, 'k)]) in
letcc 'case <- (copair 'a_finish 'b_finish) in
[sum 'case]
```

## Usage

Install with `dune build` + `dune install`

`moo --help` will display all possible options, namely
- `moo repl` launches the REPL
- `moo <PROGRAM>` or `moo run <PROGRAM>` will run a program to completion

Unfortunately as the syntax is still evolving, the test files remain the best example to see syntax.
