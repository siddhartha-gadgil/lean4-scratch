open Nat

partial def ackermann : Nat → Nat → Nat 
| 0, n => n + 1
| (succ m), 0 => ackermann m 1
| (succ m), (succ n) => ackermann m (ackermann (succ m) n)

#eval ackermann 3 3

-- #eval ackermann 4 2