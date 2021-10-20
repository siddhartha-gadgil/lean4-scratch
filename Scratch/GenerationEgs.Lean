import Scratch.ProdSeq
import Scratch.ExprAppl
import Scratch.ExprRw
import Scratch.IntrosRwFind
import Lean.Meta
import Lean.Elab
open Lean Meta Elab Term Tactic
open ProdSeq

namespace GenerationEgs
def isType : Expr → MetaM Bool :=
  fun exp => 
    do
      let tp ← inferType exp
      return tp.isSort

def isle (type: Expr)(evolve : List Expr → MetaM (List Expr))(init : List Expr) : 
        MetaM (List Expr) := 
    withLocalDecl Name.anonymous BinderInfo.default (mkConst ``Nat)  $ fun x => 
        do
          let l := x :: init
          let evl ← evolve l
          let evt ← evl.filterM (isType)
          let exported ← evl.mapM (fun e => mkLambdaFVars #[x] e)
          let exportedPi ← evt.mapM (fun e => mkForallFVars #[x] e)
          return exported ++ exportedPi

def isleSum (types: List Expr)(evolve : List Expr → MetaM (List Expr))(init : List Expr) : 
        MetaM (List Expr) := 
        match types with
        | [] => return []
        | h :: t => 
          do
            let tail ← isleSum t evolve init
            let head ← isle h evolve init
            return head ++ tail        

def generate (mvar: MVarId): List Expr → TermElabM (List Expr) :=
  fun l => do
    logInfo m!"initial list {l}"
    logInfo m!"initial types {← types l}"
    let initTypes ← l.filterM (fun x => liftMetaM (isType x))
    logInfo m!"initial terms that are types : {initTypes}"
    let gen2 ← iterAppRWM 3 mvar l
    -- logInfo m!"rw-app 2 list {gen2}"
    logInfo m!"rw-app 2 types {(← types gen2).eraseDups}"
    logInfo m!"rw-app 2 equalities {(← types gen2).eraseDups.filter (Expr.isEq)}"
    let gen3 ← isleSum initTypes (iterAppRWM 2 mvar) l
    logInfo m!"from island : {gen3}"
    return gen2 ++ gen3

syntax (name:= generateEg) "generate_from" term : tactic
@[tactic generateEg] def genImpl : Tactic := 
    fun stx =>
    match stx with 
    | `(tactic|generate_from $t) =>
        withMainContext do
          let pl ← Tactic.elabTerm t none
          let l ← unpack pl 
          let mvar ← getMainGoal
          let gl ← generate mvar l
          assignExprMVar mvar (Lean.mkConst `Unit.unit)
          return ()
    | _ => throwIllFormedSyntax

example (n m p: Nat)(eq1 : n = m)(eq2 : m = p)(P : Nat → Type)
      (f : Nat → Bool)(g: Bool → Nat) : Unit := by 
      generate_from eq1 ::: eq2 ::: g ::: P ::: 3 ::: n ::: f ::: Nat ::: ()