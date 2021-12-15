-- experiments with caching

import Scratch.Eg5

#check xxx

#check getX

#eval getX

#eval incX

#eval getX

#eval getX

#eval incX 

#eval getX

-- #check incTask

-- #eval incTask

-- #eval getX

-- #eval incTask

def snapShot : IO Nat := 
  do
    let value ← getX
    return whnf! value

#eval snapShot
#print snapShot

def s : IO Nat := getXRef xxx

#eval s

initialize xx : IO.Ref (Nat) ← IO.mkRef (← s)

#print xx