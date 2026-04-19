data i64 = int

data peano = Z | S(peano)

let rec pti_aux (n : peano, acc : i64, k : -i64) =
  match n {
  | Z -> acc . k
  | S(m) -> pti_aux . (m, acc + 1, k)
  }

let peano_to_i64 (n : peano, k : -i64) =
  pti_aux . (n, 0, k)

do{k}
  let p = S(S(S(S(Z)))) in
  peano_to_i64 . (p, k)
