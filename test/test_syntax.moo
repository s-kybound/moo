data i64 = raw64
codata ci64 = raw64
/*
desugared:
type i64 = data raw64
type ci64 = codata raw64
*/

data list<A> = 
    | Nil 
    | Cons(A, list<A>)

/*
desugared: 
type list<A> = data
    | Nil 
    | Cons(A, [CBV]list<A>)
*/

codata stream<A> =
    | Head(~A)
    | Tail(-stream<A>)

/* 
desugared:
type stream<A> = codata
    | Head(~A)
    | Tail(-[CBN]stream<A>)
*/

let rec ones : stream<i64> = 
    match {
        Head(k: -i64) -> 1 . k
        Tail(k: -stream<i64>) -> ones . k
    }

/*
desugared:
let ones =
   fix[ones] {
       match {
	   Head(k: -i64) -> 1 . k
	   Tail(k: -stream<i64>) -> ones . k
       }
   }
*/

/*
procedure sugar follows what we have learned from minimu.
proc id(x, k) { k . x }

desugared:
let rec id = 
  match {
    (x, k) -> k . x
  } 

this desugaring allows proc to be either cbv or cbn depending on the usage context!
*/

proc list_map<A, B>(f: fun<A, B>, xs: list<A>, k: -list<B>) {
    match xs {
        Nil -> k . Nil 
        Cons(x, xs') ->
            let x' <- f(x) in
            let xs'' <- list_map(f, xs') in
            k . Cons(x', xs'')
    }
}

proc stream_map<A, B>(f : fun<A, B>, xs : stream<A>, k : -stream<B>) {
    match k {
        Head(k1: -B) -> 
            let x <- { k -> xs . Head k } in
            let x' <- f(x) in
            k1 . x'
        Tail(k2: -stream<B>) -> 
            let xs' <- { k -> xs . Tail k } in
            stream_map(f, xs') . k2
    }
}

/* conversion between cbn and cbv modes can be done at matches. 
 * as the bound variable is forced to be in the canonical form for that
 * match, we can annotate as necessary 
 * this trick is only available for data expressions and codata continuations */

proc force_list<A>(xs: [CBN]list<A>, k: -[CBV]list<A>) {
    match xs {
        xs' -> xs' . k
    }
}
    
proc lazify_list<A>(xs: [CBV]list<A>, k: -[CBN]list<A>) {
    match xs {
        xs' -> xs' . k
    }
}

/*
desugared:
let lazify_list =
    match {
        (A_temp:type, tap_k) ->
            type A <- A_temp in
            match tap_k {
                (xs: [CBV]list<A>, app_k: -[CBN]list<A>) ->
                match xs {    
                    xs' -> xs' . app_k
                }
            }
    }
*/
