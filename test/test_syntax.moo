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

proc stream_map<A, B>(f : fun<A, B>, xs : stream<A>, k : -stream<B>) =
    match k {
        Head(k1: -B) ->
            let x <- { k -> xs . Head k } in
            let x' <- f(x) in
            k1 . x'
        Tail(k2: -stream<B>) -> 
            let xs' <- { k -> xs . Tail k } in
            stream_map(f, xs') . k2
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

// forcing and lazifying for codata is a little harder, but can be encoded too

codata wrapper<A> =
    | Unwrap(~A)
    | Lazify(-[CBN]wrapper<A>)
    | Force(-[CBN]wrapper<A>)

let rec foo: [CBN]wrapper<i64> = { k ->
    println("Constructing wrapper");
    let rec i_foo: [CBV]wrapper<i64> <-
        match {
	    Unwrap(k: -i64) -> 42 . k
	    Lazify(k: -[CBN]wrapper<i64>) -> foo . k
	    Force(k: -[CBV]wrapper<i64>) -> i_foo . k
    	} 
    in
    i_foo k
}

let rec foo: [CBV]wrapper<i64> = { k ->
    println("Constructing wrapper");
    let rec i_foo: [CBN]wrapper<i64> <-
        match {
	    Unwrap(k: -i64) -> 42 . k
	    Lazify(k: -[CBN]wrapper<i64>) -> i_foo . k
	    Force(k: -[CBV]wrapper<i64>) -> foo . k
    	} 
    in
    i_foo k
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

// array syntax?

/*
a[i] desugared to  a . Get(i)
a[i] <- v  desugared to a . Set(i, v)

// get item command
a[i] -> k
// sugar?
a[i] => { k -> a[i] -> k }
// setting item command is fine as is

// set item command
a[i] <- v | k
 */
