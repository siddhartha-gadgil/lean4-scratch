import Scratch.ExprAppl
import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean
open ToExpr

-- Attempt to put together lists of terms. Using products is better.

universe u

inductive TermSeq where
  | empty : TermSeq
  | cons : {α : Type} → (a : α) → (tail: TermSeq) → TermSeq
  | consProp : {α : Prop} → (a: α ) → (tail: TermSeq) → TermSeq

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

def prependExpr: MetaM Expr → MetaM Expr → MetaM Expr := 
        fun (head : MetaM Expr) (tail : MetaM Expr) =>
          do
            let h ← head
            let t ← tail
            let ht ← inferType h
            let e ← 
                if (← isProp ht)
                then
                  mkAppM ``TermSeq.consProp #[h, t]
                else
                  let htt ← inferType ht
                  let typtyp := mkSort levelOne
                  if ← isDefEq htt typtyp then
                    mkAppM ``TermSeq.cons #[h, t]
                  else t

def pack (xs : List Expr) : MetaM Expr :=
  do 
      let empty : MetaM Expr := return mkConst `TermSeq.empty
      let terms: List (MetaM Expr) := xs.map (fun x => return x)
      let expr : MetaM Expr := terms.foldr prependExpr empty
      return ← expr

partial def unpack : Expr → MetaM (List Expr) :=
  fun expr => 
  do 
    let mvar ←  mkFreshExprMVar none
    let tmvar ← mkFreshExprMVar (mkConst `TermSeq)
    let sExp ←  mkAppM ``TermSeq.cons #[mvar, tmvar]
    let spExp ←  mkAppM ``TermSeq.consProp #[mvar, tmvar]
    if ← isDefEq sExp expr then
      let prev ← unpack tmvar
      return mvar :: prev
    else 
      if ← isDefEq spExp expr then
        let prev ← unpack tmvar
        return mvar :: prev
      else return []

partial def append : Expr → Expr → MetaM Expr :=
    fun x1 x2 => 
      do 
        let l1 ← unpack x1 
        let l2 ← unpack x2 
        return ← pack (l1.append l2)

def applyStep (ts: Expr) : TermElabM Expr :=
  do
    let l ← unpack ts
    let ll ← applyPairs l l
    let out ← pack (l.append ll)
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
            let e ← 
                TermSeq.prependExpr h t
            return e
      let expr : TermElabM Expr := terms.foldr combine empty
      return ← expr
  | _ => Elab.throwIllFormedSyntax

open Nat

def egTermSeq := #⟨(1 : Nat), 3, 5, succ, zero, double⟩

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

def egInLam := 
    fun (f: Nat → Nat) => 
      let seq := #⟨1, 3, 5, f⟩
      let ev := applyall! seq
      prod! ev

#print egInLam
#check egInLam double
#reduce egInLam double
#reduce egInLam (fun x => x  * x)   


def typInSeq? (α : Expr) : Expr → MetaM (Option Expr) :=
  fun x =>
    do
      let xs ← TermSeq.unpack x
      return ← typInList? α xs

open Lean.Elab.Tactic 

def seekInSeq (ts: Expr) : TacticM Unit :=
  do
    let mvar ← getMainGoal
    let target ← getMainTarget
    let found ← typInSeq? target ts
    match found with
    | some x => 
      do
        assignExprMVar mvar x
        replaceMainGoal []
        return ()
    | none => 
      throwTacticEx `findInSeq mvar m!"did not find {target} in sequence"
      return ()

syntax (name:= termseqFind) "findInSeq" term : tactic
@[tactic termseqFind] def termseqfindImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic|findInSeq $s ) => 
    withMainContext do
      let t ← elabTermForApply s 
      seekInSeq t
  | _ => Elab.throwIllFormedSyntax

def modusPonensVerbose (α β : Type) : α → (α → β) → β := by
      intros x f
      let base := #⟨f, x⟩
      let step := applyall! base
      findInSeq step

theorem modus_ponens_verbose (α β : Prop) : α → (α → β) → β := by
      intros x f
      let base := #⟨f, x⟩
      let step := applyall! base
      findInSeq step
  
#reduce modus_ponens_verbose
#reduce modusPonensVerbose
