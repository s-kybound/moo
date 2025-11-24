type (fun a b) = (a & ~b)
type identity = (forall t (fun t t)+)

let [id : identity+] <-
  (gen t ->
   (cosplit [v : t], [k : ~t] -> 
   [v k]))
in
letcc [id_gen : identity-] <- 
  (inst [(forall v (fun v unit+)+)] unit+
    (let [new_id : (fun unit+ unit+)+] -> 
      [new_id '((), done)]))
in
[id_gen id]