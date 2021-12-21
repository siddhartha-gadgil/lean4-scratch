open Nat

partial def ackermann : Nat → Nat → Nat 
| 0, n => n + 1
| (succ m), 0 => ackermann m 1
| (succ m), (succ n) => ackermann m (ackermann (succ m) n)

#eval ackermann 3 3

-- #eval ackermann 4 2

def slowMin(n: Nat) : Nat := Id.run do
  let mut min := 0
  for i in [0:n] do
    for j in [0: n] do
      for k in [0: n] do
        if i + j + k < min then
          min := i + j + k
      if i + j < min then
        min := i + j
  return min
