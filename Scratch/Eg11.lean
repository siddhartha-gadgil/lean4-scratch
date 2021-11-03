import Scratch.Eg10
import Lean.Meta
import Lean.Elab
open Lean Meta Elab Term

set_option pp.all true

#check cache! (3: Nat) at hello

#eval getCached? `hello

def egLoad :=  load! hello

#eval egLoad


#check cache! (fun (x: Nat) => x * 2) at func 

#check (load! func)

def h := getCached? `hello

#eval h

def ff := getCached? `func

#eval ff

def fff := load! func

#check cache! 10 at ten

def tten := load! ten

#eval tten

syntax(name:= defeq) term "defeql" term: term
@[termElab defeq] def defEqImpl : TermElab := 
  fun stx type =>
  match stx with
  | `($x defeql $y) => do
    let t ← elabTerm x none
    let s ← elabTerm y none
    if ← isDefEq t s then
      return mkConst `Bool.true
    else  return mkConst `Bool.false    
  | _ => throwIllFormedSyntax

def chkeq := (fun (x: Nat) => #[x, Nat.succ x]) defeql (fun (y: Nat) => #[y, y + 1])
#eval chkeq

#check @inferInstance (Hashable (Nat → Nat))