/* File to demonstrate some of moo's top-level syntax,
 * to explain it's module evaluation order.
 */

// open item, not compiled by the IR system.
open Syntax

// use item, not compiled by the IR system.
use Syntax.Ast as A

// the top level is either declarations or expressions.

// data declarations
data i64 = raw64

type lazy_i64 = data[cbn] raw64

codata co64 = raw64

codata[cbv] co_lazy_i64 = raw64



// term definitions
// definitions must be fully typed!
let x : i64 = 42

let y : lazy_i64 = 42

let z : co64 = 42
// sugar for 42 . { z -> <rest of module> }


// procedures are sugar over call-by-value codata matchers
// note that there is no return type, you must supply an exit continuation.
proc id (x : i64, k : -i64) {
    x . k
}

// sugar for
let id : codata[cbv] (i64, -i64) =
  match {
    (x : i64), (k : -i64) -> x . k
  }

// top level expressions
1

id
// desugared into id . { _ -> <rest of module> }

//do syntax - to execute commands
do{k}
  id . (42, k)

// desugared into a mu command!
{ k -> id . (42, k) }

do
  exit . 0

// desugared into
{ _ -> exit . 0 }