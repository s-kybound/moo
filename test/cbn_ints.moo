data i64 = raw64   // definition of data i64
codata ci64 = raw64 // definition of codata i64

proc expensive1(in:[CBN]i64, out:-[CBN]i64) {
    // some expensive computation
}

proc expensive2(in:[CBN]i64, out:-[CBN]i64) {
    // defer idiom
    let out <- /* do something with out */ in
    // some expensive computation
}

proc main() {
    let x:i64 <- 42 in    // CBV by default
    let y:-ci64 <- 42 in  // CBN by default
    let y:i64 <- x + y in // shadowing y
                          // to note, x + y is sugar for
                          // { k -> +(x, y | k) }
                          
    let v:i64 <- { k -> +(x, y | k) } in

    { v:cbv- -> ... } . { k:cbv+ -> +(x, y | k) } 

    match y with {
        y:[CBN]i64 ->
        let z <- { k -> expensive1.(y, k) } in
        let a <- { k -> expensive2.(z, k) } in
        let if_expr <-
            match { 
                True -> a . done
                False -> z . done
            } 
        in
        if_expr . True
    }
}