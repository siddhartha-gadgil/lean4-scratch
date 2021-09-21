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



syntax (name:= termseq) "#⟨" term,* "⟩" : term
-- macro_rules
--   | `( #⟨$[$xs:term],*⟩ ) => 
--     xs.foldr (fun head accum => 
--       do 
--         let tail ← accum
--         return ← `(TermSeq.cons $head $tail)) `(TermSeq.empty)

@[termElab termseq] def termSeqImpl : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `( #⟨$[$xs:term],*⟩ ) => 
    do 
      let terms := xs.map (fun x => elabTerm x none)
      let empty : TermElabM Expr := return mkConst `TermSeq.empty
      let combine : TermElabM Expr → TermElabM Expr → TermElabM Expr := 
        fun (head : TermElabM Expr) (tail : TermElabM Expr) =>
          do
            let h ← head
            let t ← tail
            let e ← mkAppM ``TermSeq.cons #[h, t]
            return e
      let expr : TermElabM Expr := terms.foldr combine empty
      return ← expr
  | _ => Elab.throwIllFormedSyntax

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