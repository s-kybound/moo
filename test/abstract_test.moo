// testing if abstract types remain abstract
let test : [A : <-] data (A, ~A) = (1, exit);;

// this should fail to typecheck since A is abstract
// and we are attempting to use it with a concrete type
do{k}
  match test {
    abstract, _ -> abstract . (exit : -data int)
  }