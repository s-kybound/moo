/* This program should fail to typecheck 
 * because it is unable to infer a type 
 * for x and y. */

do
  let x = { _ -> exit . 0 } in
  let y = { _ -> exit . 0 } in
  x . y

match { x, y ->
  let a = { k -> x . (1, exit) } in
  let b = { k -> y . (1, exit) } in
  exit . 1
}


/* It turns out that if we have an unused "empty" variable, the typechecker is smart enough
 * to complain about it and reject the program, which is a nice bonus!
 */