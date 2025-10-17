# curry-howard correspondence in relation to the calculus

How then can we get expressiveness back? We turn to the Curry-Howard correspondence for inspiration.

With just cut, we only have falsity/negation - a continuation can be seen as having the type (A -> FALSE). At minimum, we
need some logical connective (other than implication) to restore a full logical system. There are several options, namely

- conjunction (products)
- disjunction (sums)

We choose to go with these as they are simpler than a lambda abstraction as a primitive data type. As disjunction in a dual
calculus has been more well studied through case and cocase, we opt to explore conjunction by introducing a pair, and
demonstrate how just having the pair and its consumer split enables us to restore full expressiveness. We also introduce 
the polar duals of pairs and splits, the cosplit and copair.

# what is the polar dual of pair and split?

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
{* a is the input value, 'k is the exit continuation *}
<(cosplit a 'b M) | (copair x 'k)> -> M[x/a, 'k/'b]
```

We also have the negative function abstraction:
```
{* a is the input value, 'k is the exit continuation *}
<(pair x 'k) | (split a 'b M)> -> M[x/a, 'k/'b]
```

In this case, the consumer tells us what to do!

A personal hypothesis behind why cosplit is not as well known as cocase is because cocase and case are usually used as general pattern 
matchers against algebraic datatypes, which encode for both products and sums.

# cutlet-style syntax


Cuts are nice, but managing raw cuts is difficult to look at, especially when composing several of them in tandem.
So I also sought a way to make them more pleasing to the eye.

Take this example from `sum.moo` which encodes the left injection of a sum, using cuts and products:
```
  (cosplit v 'k -> [ (cosplit 'a_next 'b_next -> [v 'a_next]) 'k ])
```
This expresses a producer of a negative product: given a continuation 'k expecting a choice ('a_next/'b_next), we immediately choose the left branch and send along v. It works, but the nested, back-to-back cuts make the control flow hard to scan.

We see that many computations are of the shape `[ (destruct value -> do something else ) v ]`.
Compare this to languages like SML, which are of the shape
```
destruct value <- v in
do something else
```
And there is an immediate translation! so for cuts of shape `[(destructure.M) v]` we can reshape this as `destructure <- v in M`.

Encoding it using this idea, we get this:
```
  (cosplit v 'k ->
   letcc 'k <- 'k in {* entirely unnecessary, but one can now see why these are called let-style *}
   cosplit 'a_next 'b_next <- 'k in
   [v 'a_next])
```
Tada! by representing the immediate cut as `cosplit ... <- 'k in`, we get a much cleaner syntax. and by introducing a way to define producers with names (and the single consumuer that they expect), we get
```
{* defp wraps the inner statements in a Mu encoding *}
defp inl 'ap =
  cosplit v 'case <- 'ap in
  cosplit 'a_next 'b_next <- 'case in
  [v 'a_next]
{*
  this desugars to 
  (letcc 'ap -> [(cosplit v 'case -> [(cosplit 'a_next 'b_next -> [v 'a_next]) 'case])'ap])
*}
;;
```
Which is much cleaner. This is also an argument for the humble `cosplit`/`split` as compared to `comatch`/`match` and `cocase`/`case`, if using simple products is sufficient for your program, as the equivalent syntax for `comatch` and the like would be like

```
comatch <- 'ap in
| Ap a b -> <some statement>
| _ -> <other statement>
```
which is still readable, but more verbose especially when all you need is a simple branch choice.
