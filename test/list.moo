

/*
let rec head[A <-](xs : list<A>, out : ~A) =
   let head = head in
   match xs {
   | Cons(head, _) -> head . out
   | Nil -> exit . 1
   }
*/

data list<A> = Cons(A, +list<A>) | Nil
let rec length[A <-](xs : list<A>, out : -data int) =
  match xs {
  | Nil -> 0 . out
  | Cons(_, rest) -> 
    let recur = { k -> length.(rest, k) } in
    +(1, recur | out)   
  }

do
  letcc ap = (Cons(1, Nil), exit) in
  length.ap