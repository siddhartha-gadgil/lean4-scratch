import Scratch.ExprAppl
import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean
open ToExpr

inductive TermSeq where
  | empty : TermSeq
  | cons : {α : Type} → (a : α) → (tail: TermSeq) → TermSeq

def mkProd {α β : Type} (a: α ) (b: β) : Prod α β := ⟨a, b⟩

def foldExps : List Expr → TermElabM Expr  
  | [] => return (mkConst `Unit.unit)
  | x :: ys => 
    do
      let tail ← foldExps ys
      let exp ← 
        mkAppM' (Lean.mkConst `mkProd) #[x, tail]
      return exp

namespace TermSeq
/-
def prodType : TermSeq → Type 
  | empty => Unit
  | @cons α a tail => Prod α (prodType tail)

def asProd : (ts: TermSeq) → prodType ts
  | empty => (() : Unit)
  | cons  a tail => (a, asProd tail)
-/

def pack (xs : List Expr) : MetaM Expr :=
  do 
      let empty : MetaM Expr := return mkConst `TermSeq.empty
      let combine : MetaM Expr → MetaM Expr → MetaM Expr := 
        fun (head : MetaM Expr) (tail : MetaM Expr) =>
          do
            let h ← head
            let t ← tail
            let e ← mkAppM ``TermSeq.cons #[h, t]
            return e
      let terms: List (MetaM Expr) := xs.map (fun x => return x)
      let expr : MetaM Expr := terms.foldr combine empty
      return ← expr

partial def unpack : Expr → MetaM (List Expr) :=
  fun expr => 
  do 
    let mvar ←  mkFreshExprMVar none
    let tmvar ← mkFreshExprMVar (mkConst `TermSeq)
    let sExp ←  mkAppM ``TermSeq.cons #[mvar, tmvar]
    if ← isDefEq sExp expr then
      let prev ← unpack tmvar
      return mvar :: prev
    else 
      return []

def applyStep (ts: Expr) : TermElabM Expr :=
  do
    let l ← unpack ts
    let ll ← listApps l l
    let out ← pack ll
    return out


def prodExpr (ts: Expr) : TermElabM Expr :=
  do
    let xs ← TermSeq.unpack ts 
    let exp ← foldExps xs
    return exp

end TermSeq


syntax (name:= termseq) "#⟨" term,* "⟩" : term
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

open Nat

def egTermSeq := #⟨1, 3, 5, succ, zero, double⟩

#check egTermSeq

syntax (name:= termseqProd) "prod!" term : term
@[termElab termseqProd] def termseqProdImpl : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `( prod! $s ) => 
    do
      let t ← elabTerm s none
      let e ← TermSeq.prodExpr t
      return e
  | _ => Elab.throwIllFormedSyntax

  
def egTermSeqProd := prod! egTermSeq

#check egTermSeqProd
#reduce egTermSeqProd

syntax (name:= termseqApply) "applyall!" term : term
@[termElab termseqApply] def termseqApplyImpl : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `( applyall! $s ) => 
    do
      let t ← elabTerm s none
      let e ← TermSeq.applyStep t
      return e
  | _ => Elab.throwIllFormedSyntax

def appliedSeq := applyall! egTermSeq
#check appliedSeq
#reduce prod! appliedSeq
