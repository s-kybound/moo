(*
 in untyped moo, we can represent numbers with pairs:
 Z - 0
 (pair S Z) - 1
 (pair S (pair S Z)) - 2 etc...

 we shall experiment with this...
*)

let val <- Z in

let add <- 
  (cosplit v 'k -> 
   let new <- (pair S v) in
   [new 'k]
  )
in

let dec <- 
  (cosplit v 'k -> 
   split _ v <- v in
   [v 'k]
  )
in

letcc 'dec_neg <-
  (split v 'k ->
   split _ v <- v in
   [v 'k]
  )
in

let val <- (letcc 'a -> [add (copair val 'a)]) in
let val <- (letcc 'a -> [add (copair val 'a)]) in
let val <- (letcc 'a -> [dec (copair val 'a)]) in
let val <- (letcc 'a -> [dec (copair val 'a)]) in
[ val 'halt ]