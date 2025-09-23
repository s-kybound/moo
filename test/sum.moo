(*
    given products, A ^ B,

    we can represent sums with
    A v B = -(-(A v B))
        = -(-A ^ -B)
    
    in moo, this is best encoded with
    a cosplit of 2 continuations for A and B.
*)

defp inl 'ap =
  cosplit v 'k <- 'ap in
  cosplit 'a_next 'b_next <- 'k in
  [v 'a_next]
;;

(*
 * the above definition used to be this:    
 * [(cosplit v 'k -> [ (cosplit 'a_next 'b_next -> [v 'a_next]) 'k ]) 'next]
 * astounding!
*)

defp inr 'ap =
  cosplit v 'k <- 'ap in
  cosplit 'a_next 'b_next <- 'k in
  [v 'b_next]
;;

(* both of the definitions above can be cased on by a copair of continuations *)

let left <- (letcc 'a -> [inl (copair L 'a)]) in
let right <- (letcc 'a -> [inr (copair R 'a)]) in

letcc 'case (* (A- & B-)- *) <-
  (copair 'a_fired 'b_fired)
in
[right 'case]
