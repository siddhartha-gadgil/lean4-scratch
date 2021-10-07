import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean
open ToExpr


def applyOptM (f x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← elabAppArgs f #[] #[Arg.expr x] none (explicit := false) (ellipsis := false)
      return some expr
    catch e =>
      return none

def listAppArgs : Expr → List Expr → TermElabM (List Expr) :=
  fun f args =>
    match args with
    | [] => return []
    | x :: ys => 
      do
        let head ← applyOptM f x
        let tail ← listAppArgs f ys
        match head with
        | some expr => return expr :: tail
        | none => return tail

def applyPairs : List Expr →  List Expr  → TermElabM (List Expr)  := fun l args =>
  match l with
  | [] => return []
  | x :: ys => 
    do
      let head ← listAppArgs x args
      let tail ← applyPairs ys args
      return head ++ tail

def double: Nat→ Nat := fun x => x + x

def expList := [toExpr 1,  toExpr 3, Lean.mkConst `Nat.succ, Lean.mkConst `Nat.zero, 
              Lean.mkConst `double]

def evListEg := applyPairs expList expList

def applyPairsCuml :  List Expr  → TermElabM (List Expr)  := 
        fun l  =>
          do
            let step ← applyPairs l l
            return step ++ l 
            
def applyPairsMeta : List Expr → MetaM (List Expr) :=
  fun l => (applyPairsCuml l).run'

#eval evListEg
#check evListEg
