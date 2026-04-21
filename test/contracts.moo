data i64 = int
codata[cbv] predicate<A> = (A, -data bool)

let not_0(x : i64, k : -data bool) =
  match x {
  | 0 -> false . k
  | _ -> true . k
  }

// ensure tests the term
let ensure[B <-](tested : B, p : codata(B, -data bool), k : ~B) =
  p . (tested, { result ->
    match result {
    | true -> tested . k
    | false -> exit . 1
    }
  })

// expect tests what the term is cut with
let expect[C <-](tester : ~C, p : predicate<C>, k : C) =
  { tested -> 
    p . (tested, { result ->
      match result {
      | true -> tested . tester
      | false -> exit . 1
      }
    })
  } . k
