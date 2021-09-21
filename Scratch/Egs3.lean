import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean
open Nat 

inductive TermSeq where
  | empty : TermSeq
  | cons : {α : Type} → (a : α) → (tail: TermSeq) → TermSeq



syntax "#⟨" term,* "⟩" : term
macro_rules
  | `( #⟨$[$xs:term],*⟩ ) => 
    xs.foldr (fun head accum => 
      do 
        let tail ← accum
        return ← `(TermSeq.cons $head $tail)) `(TermSeq.empty)


partial def seqLength : Expr → MetaM Nat := fun expr =>
  do
    let mvar ←  mkFreshExprMVar none
    let tmvar ← mkFreshExprMVar (mkConst `TermSeq)
    let sExp ←  mkAppM ``TermSeq.cons #[mvar, tmvar]
    if ← isDefEq sExp expr then
      let prev ← seqLength tmvar
      return succ (succ prev)
    else 
      return zero

syntax (name:= tsl) "tsl!" term : term 

@[termElab tsl] def tslImpl : TermElab :=
  fun stx expectedType? =>
    match stx with
    | `(tsl! $s) =>
      do 
        let e ← elabTerm s none
        let l ← seqLength e
        return ← ToExpr.toExpr l 
    | _ => Elab.throwIllFormedSyntax



def ts := TermSeq.cons 3 TermSeq.empty

#eval tsl! ts
#eval tsl! #⟨3, 4, "this"⟩

#check  #⟨3, 4, "this"⟩