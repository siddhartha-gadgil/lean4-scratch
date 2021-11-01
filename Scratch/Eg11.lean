import Scratch.Eg10

set_option pp.all true

#check cache! (3: Nat) at hello

#eval getCached? `hello

def egLoad :=  load! hello

#eval egLoad


#check cache! (fun (x: Nat) => x * (2: Nat)) at func 

#check (load! func)

def h := getCached? `hello

#eval h

def ff := getCached? `func

#eval ff

def fff := load! func

#check cache! 10 at ten

#check @OfNat.ofNat

#eval  getCached? `ten
