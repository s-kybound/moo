(*
    given products, A ^ B,

    we can represent sums with
    A v B = -(-(A v B))
        = -(-A ^ -B)
    
    in moo, this is best encoded with
    a cosplit of 2 continuations for A and B.
*)

let inl (* A+ -> (A- & B-)+ *) <-
  (cosplit v 'k -> [ (cosplit 'a_next 'b_next -> [v 'a_next]) 'k ])
in

let inr (* (A- & B-)+ *) <-
  (cosplit v 'k -> [ (cosplit 'a_next 'b_next -> [v 'b_next]) 'k ])
in

let left <- (letcc 'a -> [inl (copair L 'a)]) in
let right <- (letcc 'a -> [inr (copair R 'a)]) in

letcc 'case (* (A- & B-)- *) <-
  (copair 'a_fired 'b_fired)
in
[right 'case]
