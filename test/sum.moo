{*
    given products, A ^ B,

    we can represent sums with
    A v B = ~(~A ^ ~B)
          = ~A & ~B {* KIV we are unable to negate over operators 
                     * for now, only consumers/producers *}

    this means that A+ v B+ -> ~(A+) & ~(B+) -> A- & B- !

    similarly, implication can be represented with
    A -> B = ~(A ^ ~B)
           = A & ~B

    so a function (fun A+ B+) can be encoded with A+ & B- !

    keep in mind that moo uses lisp syntax for types, 
    so the operators will come first
*}

defp [ inl : (& A+ (& A- B+)-)+ ] ['ap : (& A+ (& A- B-)-)- ] =
  cosplit [ v : A+ ] [ 'case : (& A- B-)- ] <- 'ap in
  cosplit [ 'a_next : A- ] [ 'b_next : B- ] <- 'case in
  [v 'a_next]


{*
 * a demonstration of let-style cuts!
 * the above definition used to be this:    
 * [(cosplit v 'k -> [ (cosplit 'a_next 'b_next -> [v 'a_next]) 'k ]) 'next]
 * astounding!
 *}

{* astounding, especially with types, but verbose. i want to abstract away the types. *}
type (sum a b) = (& ~a ~b)

{* this judgement turns (sum A+ B+)+ -> (& A- B-)+ ! *}

{* i also would like to abstract the function type away *}
type (fun a b) = (& a ~b)

{* this judgement turns (fun A+ B+)+ -> (& A+ B-)+ ! *}
defp [ inr: (fun B+ (sum A+ B+)+)+ ] ['ap : (fun B+ (sum A+ B+)+)- ] =
  cosplit [ v : B+ ] [ 'case : (sum A+ B+)- ] <- 'ap in
  cosplit [ 'a_next : A- ] [ 'b_next : B- ] <- 'case in
  [v 'b_next]

{* both of the definitions above can be cased on by a copair of continuations *}

let [ left : (& A- B-)+ ] <- (letcc ['a : (& A- B-)-] -> [inl (copair L 'a)]) in
let [ right : (& A- B-)+ ] <- (letcc ['a : (& A- B-)-] -> [inr (copair R 'a)]) in

letcc [ 'case : (& A- B-)- ]  <-
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
