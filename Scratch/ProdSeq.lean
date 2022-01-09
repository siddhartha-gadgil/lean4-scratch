import Lean.Meta
import Lean.Elab
open Lean Meta Elab Term

namespace ProdSeq
def splitPProd? (expr: Expr) : MetaM (Option (Expr × Expr)) :=
  do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort u)
    let β  ← mkFreshExprMVar (mkSort v)
    let a ← mkFreshExprMVar α 
    let b ← mkFreshExprMVar β 
    let f := mkAppN (Lean.mkConst ``PProd.mk [u, v]) #[α, β, a, b]
    if ← isDefEq f expr
      then
        return some (← whnf a, ← whnf b)
      else 
        -- logInfo m!"{expr} is not a PProd {f}"
        return none

def splitProd?(expr: Expr) : MetaM (Option (Expr × Expr)) :=
  do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort (mkLevelSucc u))
    let β  ← mkFreshExprMVar (mkSort (mkLevelSucc v))
    let a ← mkFreshExprMVar α 
    let b ← mkFreshExprMVar β 
    let f := mkAppN (Lean.mkConst ``Prod.mk [u, v]) #[α, β, a, b]
    if ← isDefEq f expr
      then
        return some (← whnf a, ← whnf b)
      else 
        -- logInfo m!"{expr} is not a Prod {f}"
        return none

def split? (expr: Expr) : MetaM (Option (Expr × Expr)) :=
    do
      let hOpt ← splitPProd? expr 
      let hpOpt ← splitProd? expr
      return hOpt.orElse (fun _ => hpOpt)

#eval Unit.unit

partial def unpack (expr: Expr) : MetaM (List Expr) :=
    do
      match (← split? expr) with
      | some (h, t) => h :: (← unpack t) 
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

def pack : List Expr →  MetaM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← pack ys
      let expr ← mkAppM `PProd.mk #[x, t]
      return expr

def lambdaPack : List Expr →  MetaM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← lambdaPack ys
      let tail ← mkLambdaFVars #[x] t
      let expr ← mkAppM `PProd.mk #[x, tail]
      return expr

partial def lambdaUnpack (expr: Expr) : MetaM (List Expr) :=
    do
      match (← split? expr) with
      | some (h, t) =>
        let tt ← whnf <| mkApp t h
        let tail ←  lambdaUnpack tt
        h :: tail
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

def packTerms : List Expr →  MetaM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← packTerms ys
      if ← isProof x 
      then return t  
      else 
        let expr ← mkAppM `Prod.mk #[x, t]
        return expr

syntax (name := prodHead) "prodHead!" term : term
@[termElab prodHead] def prodHeadImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(prodHead! $t) => 
    do
      let expr ← elabTerm t none
      let hOpt ← splitPProd? expr 
      let hpOpt ← splitProd? expr
      match (hOpt.orElse (fun _ => hpOpt)) with
      | some (h, t) => return h
      | none => throwAbortTerm    
  | _ => throwIllFormedSyntax

#eval prodHead! (10, 12, 15, 13)


syntax (name := prodlHead) "prodlHead!" term : term
@[termElab prodlHead] def prodlHeadImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(prodlHead! $t) => 
    do
      let expr ← elabTerm t none
      let l ← try 
        unpack expr
        catch exc => throwError m!"Error {exc.toMessageData} while unpacking {expr}"
      return l.head!   
  | _ => throwIllFormedSyntax

#eval prodlHead! (3, 10, 12, 13, ())

syntax (name:= roundtrip) "roundtrip!" term : term
@[termElab roundtrip] def roundtripImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(roundtrip! $t) => 
    do
      let expr ← elabTerm t none
      let l ← unpack expr
      -- logInfo l
      -- logInfo m!"size : {l.length}"
      let e ← pack l
      let ll ← unpack e
      let ee ← pack ll
      return ee
  | _ => throwIllFormedSyntax

syntax (name:= justterms) "terms!" term : term
@[termElab justterms] def justtermsImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(terms! $t) => 
    do
      let expr ← elabTerm t none
      let l ← unpack expr
      -- logInfo l
      -- logInfo m!"size : {l.length}"
      let e ← packTerms l
      return e
  | _ => throwIllFormedSyntax

#check roundtrip! (3, 10, "twelve", 13, ())

#check fun x y: Nat => roundtrip! (x + x * y, ())

inductive P: Nat → Nat → Type where

#check fun x y: Nat => fun p : P x y => roundtrip! (x + x * y, p, ())

infixr:65 ":::" => PProd.mk

#check roundtrip!  (rfl : 1 = 1) ::: "this" ::: 4 ::: 3 ::: ()

#eval terms! "hello" ::: (rfl : 1 = 1) ::: "this" ::: 4 ::: 3 ::: ()

end ProdSeq