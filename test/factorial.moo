data i64 = raw64

/* non-tail recursive version of factorial, written in
 * traditional style. 
 */
proc rec factorial(x : i64, k : -i64) {
  match x {
  | 1 -> 1 . k
  | x ->
    let acc <- { k -> factorial . (x - 1, k) } in
    (x * acc) . k
  }
} 

({ k -> factorial . (4, k) })

/* non-tail recursive version of factorial, written in
 * a style more natural for the dual language.
 */
proc rec factorial(x : i64, k : -i64) {
  match x {
  | 1 -> 1 . k
  | x -> factorial . (x - 1, { result -> (x * result) . k })
  }
}  

({ k -> factorial . (4, k) })

proc rec factorial_tco(counter : i64, acc : i64, k : -i64) {
    match counter {
    | 1 -> acc . k
    | x ->
       let new_counter <- x - 1 in
       let new_acc <- acc * x in
       factorial_tco . (new_counter, new_acc, k)
    }
}  

proc factorial(x : i64, k : -i64) {
  factorial_tco . (x, 1, k)
} 

({ k -> factorial . (4 , k) })