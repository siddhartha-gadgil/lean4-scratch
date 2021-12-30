import Scratch.ProdSeq
import Scratch.ExprAppl
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

set_option pp.all true

def generate1 (mvar: MVarId): List Expr → TermElabM (List Expr) :=
  fun l => do
    logInfo m!"initial list {l}"
    logInfo m!"initial types {← types l}"
    let initTypes ← l.filterM (fun x => liftMetaM (isType x))
    logInfo m!"initial terms that are types : {initTypes}"
    let gen2 ← iterAppRWMTask 3  l [] 
-- logInfo m!"rw-app 2 list {gen2}"
    logInfo m!"rw-app 2 types {(← types gen2).eraseDups}"
    logInfo m!"rw-app 2 equalities {(← types gen2).eraseDups.filter (Expr.isEq)}"

    return l

def generate2 : List Expr → TermElabM (List Expr) :=
  fun l => do
    logInfo m!"initial list {l}"
    logInfo m!"initial types {← types l}"
    let initTypes ← l.filterM (fun x => liftMetaM (isType x))
    logInfo m!"initial terms that are types : {initTypes}"
    let gen3 ← isleSum initTypes (iterAppTask 3) l
    logInfo m!"from island : {gen3}"
    return l

def generate (mvar: MVarId): List Expr → TermElabM (List Expr) :=
  fun l => 
    do
    let l ← generate1 mvar l
    let l2 ← generate2  l
    return l

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

set_option maxHeartbeats 500000

/- Taking too long, possibly a bug
example (n m p: Nat)(eq1 : n = m)(eq2 : m = p)(P : Nat → Type)
      (f : Nat → Bool)(g: Bool → Nat) : Unit := by 
      generate_from  n ::: eq1 ::: P ::: g ::: f ::: Nat ::: () 
      -- generate_from eq1 ::: eq2 ::: P  ::: f ::: g ::: n ::: m ::: Nat ::: ()
-/