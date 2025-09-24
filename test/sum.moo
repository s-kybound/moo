{*
    given products, A ^ B,

    we can represent sums with
    A v B = -(-(A v B))
        = -(-A ^ -B)
    
    in moo, this is best encoded with
    a cosplit of 2 continuations for A and B.
*}

defp inl 'ap =
  cosplit v 'case <- 'ap in
  cosplit 'a_next 'b_next <- 'case in
  [v 'a_next]
;;

{*
 * the above definition used to be this:    
 * [(cosplit v 'k -> [ (cosplit 'a_next 'b_next -> [v 'a_next]) 'k ]) 'next]
 * astounding!
 *}

defp inr 'ap =
  cosplit v 'case <- 'ap in
  cosplit 'a_next 'b_next <- 'case in
  [v 'b_next]
;;

{* both of the definitions above can be cased on by a copair of continuations *}

let left <- (letcc 'a -> [inl (copair L 'a)]) in
let right <- (letcc 'a -> [inr (copair R 'a)]) in

letcc 'case {* (A- & B-)- *} <-
  (copair 'a_fired 'b_fired)
in
[right 'case]

{*
what would case look like?

producers: (inr x) (inl y)

consumers: (case (x -> ...) (y -> ...))

producers: (cocase (x -> ...) (y -> ...))

consumers: (outr x) (outl y)

{* immediately invoked statement syntax *}
case <- sum in
| left -> [something]
| right -> [something]

cocase <- sum in
| left -> [something]
| right -> [something]

and the more generic comatch/match
syntax matches more with the cocase/case syntax

{* immediately invoked cut syntax *}
co/match <- sum in
| A b c d ->
| E f g ->
| H i ->
| J -> 

{* producer/consumer syntax *}
(match (A b c d -> ...)
       (E f g -> ...)
       (H i -> ...)
       (J -> ...))

etc...
*}
