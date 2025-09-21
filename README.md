# moo: a dual language to explore the dual mu mu-tilde calculus

moo is a tiny, dual, cut‑centric calculus meant to answer:

- What is the smallest set of data connectives, together with μ/μ̃ and cut, that regains the expressiveness of the λ‑calculus—first simply (untyped), then with types (STLC), and finally with impredicative polymorphism (System F)?

- Can we do this while omitting λ‑abstraction as a primitive and relying instead on the dual control binders μ and μ̃?

How then can we get expressiveness back? We turn to the Curry-Howard correspondence for inspiration.

With just cut, we only have falsity/negation - a continuation can be seen as having the type (A -> FALSE). At minimum, we
need some logical connective (other than implication) to restore a full logical system. There are several options, namely

- conjunction (products)
- disjunction (sums)

We choose to go with these as they are simpler than a lambda abstraction as a primitive data type. As disjunction in a dual
calculus has been more well studied through case and cocase, we opt to explore conjunction by introducing a pair, and
demonstrate how just having the pair and its consumer split enables us to restore full expressiveness. We also introduce 
the polar duals of pairs and splits, the cosplit and copair.

We first experiment with an untyped language, followed by the equivalent of the STLC for this calculus, followed by a 
full System F equivalent for mu mu-tilde calculus.

## what is the polar dual of pair and split?

We introduce the pair data type, which represents a product of 2 values. We also introduce the split consumer which allows
us to access the two values in the pair. In code:

```
<(pair x y) | (split a b M)> -> M[x/a, y/b]
```

We see that this expression will beta-reduce to the statement M, with x and y substituted for a and b. We see that split
is a consumer that tells us what to do next.

Our derivation of cosplit and copair comes from analysis of case and its polar dual cocase, in similar systems that introduce 
disjunction. While sum + case tells us: "what do I do after figuring that this sum value is this case?", with sum producers 
and a single case destructor, cocase + sum destructors tells us: "this cocase value knows what to do, if it gets this 
specific destructor.". In this case, cocase is the PRODUCER, and the sum comes in the form of its CONSUMERS.

In pseudocode:

```
< Left a | (case ( Left x -> M ) ( Right y -> N ))> -> M[a/x]
```

```
< (cocase (Left 'x -> M) ( Right 'y -> N )) | Left 'k > -> M['k/'x]
```

We see that the difference between sum/case and cocase/sum destructors is that the notion of "what to do next" is transferred from the
consumer, in the form of case, to the producer, in the form of cocase.

Hence, in similar fashion, we flip this notion to the producer in the cosplit COdata type, having the cosplit dictate what to do next, 
and have the product be transferred over to the consumer side, in the form of the copair!

In pseudocode:
```
<(cosplit 'x 'y M) | (copair 'a 'b)> -> M['a/'x, 'b/'y]
```

With cosplit, we actually are able to restore the function/implication data type as a form of codata! Like so:
```
(* a is the input value, 'k is the exit continuation *)
<(cosplit a 'b M) | (copair x 'k)> -> M[x/a, 'k/'b]
```

We also have the negative function abstraction:
```
(* a is the input value, 'k is the exit continuation *)
<(pair x 'k) | (split a 'b M)> -> M[x/a, 'k/'b]
```

In this case, the consumer tells us what to do!

A personal hypothesis behind why cosplit is not as well known as cocase is because cocase and case are usually used as general pattern 
matchers against algebraic datatypes, which encode for both products and sums.
