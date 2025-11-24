type (fun a b) = (a & ~b)
type (sum a b) = (~a & ~b)

let [ inl : (fun unit+ (sum unit+ counit-)+)+ ] <-
  (cosplit [ v : unit+ ], [ 'case : (sum unit+ counit-)- ] ->
   cosplit [ 'a_next : unit- ], [ 'b_next : counit+ ] <- 'case in
   [v 'a_next])
in
let [ L : (sum unit+ counit-)+ ] <- 
    (letcc [k : (sum unit+ counit-)-] -> [inl '((), k)]) 
in
letcc ['case : (sum unit+ counit-)-] <- '(done, codone) in
[L 'case]
