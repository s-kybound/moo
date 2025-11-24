type (sum a b) = (~a & ~b)
type (fun a b) = (a & ~b)
type cobool = (sum unit+ unit+)
type mod = (exists t (t * (fun t cobool+)+)+)

letcc [match : cobool-] <-
  ‘(done, (split -> [() done]))
in
letcc [program : mod-] <- 
  (unpack x ->  
    (let [module : (x * (fun x cobool+)+)+] ->
     split [t : x] [pred : (fun x cobool+)+] <- module in
     [pred ‘(t, match)]))
in
let [md : mod+] <- 
  (pack [mod] unit+
    ((), (cosplit [v : unit+] [k : cobool-] ->
          cosplit [l : unit-] [r : unit-] <- k in
          [v l])))
in
[md program]
