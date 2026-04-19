data i64 = int

// loops in moo can be implemented using recursion, much like
// in functional languages.
// this is a TCO (tail call optimized) loop, so it won't blow the stack. 
let rec loop(v: i64, out: -i64) =
  match v {
    0 -> v . out
    _ -> loop . (v - 1, out)
  }

do{out}
    loop . (4, out)

// but we can do better. the more natural way is to write
// recursive continuations directly instead of using procedures.
// this can be more efficient, implementing the same loop in an iterative style.
do{out}
    letcc rec loop_k : -i64 = { v -> 
        match v {
            0 -> v . out
            _ -> loop_k . (v - 1)
        } 
    } in
    loop_k . 4

// while[break = br, continue = k] pred {
//    body
// }
letcc break = br in
letcc continue = k in
letcc rec while_k : -bool =
    match {
        true ->
            let _ = { continue -> body } in
            while_k . pred
        false -> () . break
    }
    while_k . pred

// c-style for loops look like they will be difficult to
// implement in this language.

// loop[continue = k] {
//   body
// }
letcc continue = k in
letcc rec loop_k : -unit =
    { _ ->
       let _ = { continue -> body } in
       loop_k . () 
    }
    in
    loop_k . ()

// perhaps iterator style loops are more natural