data bool = True | False
data i64 = int
codata predicate<A> = A, -bool

proc not_0(x : i64, k : -bool) {
  match x {
  | 0 -> False . k
  | _ -> True . k
  }
}

// ensure tests the term
proc ensure[A : <-](tested : A, p : predicate<A>, k : ~A) {
  p . (tested, { result ->
    match result {
    | True -> tested . k
    | False -> exit . 1
    }
  })
}

// expect tests what the term is cut with
proc expect[A : <-](tester : ~A, p : predicate<A>, k : A) {
 { tested -> 
   p . (tested, { result ->
     match result {
     | True -> tested . tester
     | False -> exit . 1
     }
   })
 } . k
}

ensure . (0, not_0, { x -> x })
