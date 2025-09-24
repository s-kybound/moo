{*
  now given our full encoding of sums, we can implement
  a proper encoding of numbers, moreso than the primitive one
  in arith.moo.

  A number is of the type

  type number = (S * number) | Z

  it's best represented using codata, with cosplit.
*}

let z {* number+ *} <-
  (cosplit 's_case 'z_case -> [unit 'z_case])
in

{* there is a need to encode the s constructor as
 * a function *}
{* number+ -> number+ *}
let s <-
  (cosplit v 'k ->
    [(cosplit 's_case 'z_case -> [(pair S v) 'z_case]) 'k]
  )
in

{* with all of this, 'ifz now degrades into effectively a copair *}
let ifz <-
  (cosplit num cases ->
    split 'zero_case 'succ_case <- cases in
    [num (copair 'succ_case 'zero_case)])
in

let zero <- z in 
let one <- (letcc 'k -> [s (copair zero 'k)]) in
let result <- (letcc 'k -> 
  [ifz (copair one (pair (let z -> [is_zero 'k]) (let s -> [not_zero 'k])))]
) in
[work_in_progress 'halt]