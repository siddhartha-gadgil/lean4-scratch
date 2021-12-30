import Scratch.ExprAppl
import Scratch.ExprRw
import Scratch.ConstDeps
import Lean.Meta
import Lean.Elab
import Std.Data.HashMap
import Std.Data.HashSet
open Std
open Lean
open Meta
open Elab
open Lean.Elab.Tactic

-- unused code from ExprRw, mostly obsolete approaches either at low level or for iteration

def rwPushEq  (mvarId : MVarId) (e : Expr) (heq : Expr) 
      (symm : Bool := false): MetaM (Expr × Nat) :=
  do
    let t ← inferType e
    let rwr ← Meta.rewrite mvarId t heq symm
    let pf := rwr.eqProof
    -- let tt := rwr.eNew
    let pushed ← mkAppM `Eq.mp #[pf, e]
    return (pushed, rwr.mvarIds.length)

def rwActOptM (mvarId : MVarId) (e : Expr) (heq : Expr) 
      (symm : Bool := false) : MetaM ( Option Expr) :=
      do
        try
          let res ← rwPushEq mvarId e heq symm
          return some res.1 
        catch e =>
          return none

def rwListArgs (mvarId : MVarId)(symm: Bool) : Expr → List Expr → MetaM (List Expr) :=
  fun f args =>
    match args with
    | [] => return []
    | x :: ys => 
      do
        let headRW ← rwActOptM mvarId f x symm
        let headCong ← eqCongrOpt f x
        let head := headRW.orElse (fun _ => headCong)
        let tail ← rwListArgs mvarId symm f ys
        match head with
        | some expr => return expr :: tail
        | none => return tail 

def rwListArgsTask (mvarId : MVarId)(symm: Bool) : 
        List Expr → Expr → Task (MetaM (List Expr)) :=
  fun fns arg =>
    match fns with
    | [] => Task.pure (return [])
    | f :: gs => 
      Id.run do
        let headTask : Task (MetaM (Option Expr)) := 
          (Task.spawn (fun _ => rwActOptM mvarId f arg)).bind 
            fun headRWM =>
            let headCongTask := Task.spawn (fun _ => eqCongrOpt f arg)
            headCongTask.map (fun headCongM =>
             do 
              let headRW ← headRWM
              let headCong ← headCongM
              let head := headRW.orElse (fun _ => headCong)
              return head)
        let tailTask := rwListArgsTask mvarId symm gs arg
        headTask.bind $ fun head => 
              tailTask.map $ fun tail =>
                do 
                  let h ← head
                  match h with
                  | some expr => return expr :: (← tail)
                  | none => tail

def rwPairs(mvarId : MVarId)(symm: Bool) : List Expr →  List Expr  → MetaM (List Expr)  := fun l args =>
  match l with
  | [] => return []
  | x :: ys => 
    do
      let head ← rwListArgs mvarId symm  x args
      let tail ← rwPairs mvarId symm ys args
      return head ++ tail

def rwPairsTask(mvarId : MVarId)(symm: Bool) : List Expr →  List Expr  → Task (MetaM (List Expr))  := 
  fun fns l =>
  match l with
  | [] => Task.pure (return [])
  | x :: ys => 
    Id.run do
      let argEqn : Task (MetaM Bool) := 
          Task.spawn $ fun _ =>
           do 
              let type ← inferType x
              return (type.isEq) 
      let headTask : Task (MetaM (List Expr)) := 
        rwListArgsTask mvarId symm fns x
      let tailTask := rwPairsTask mvarId symm fns ys
      headTask.bind $ fun head => 
            tailTask.map $ fun tail =>
              do 
                return ((← head) ++ (← tail) ++ l).eraseDups

def rwAppCongStep(mvarId : MVarId) : Array Expr → TermElabM (Array Expr):=
  fun l =>
    let fn : Array Expr → Expr → TermElabM (Array Expr) :=     
      fun l arg =>
        do
          let type ← inferType arg
          if type.isEq
          then 
            let rws ← l.filterMapM (fun f => rwActOptM mvarId f arg)
            let rwsFlip ← l.filterMapM (fun f => rwActOptM mvarId f arg true)
            let congs ← l.filterMapM (fun f => eqCongrOpt f arg)
            let apps ← l.filterMapM (fun f => applyOptM f arg)
            return (rws.append (rwsFlip.append (congs.append (apps)))) ++ l
          else 
            let apps ← l.filterMapM (fun f => applyOptM f arg)
            return apps ++ l
    let res := Array.foldlM (fn) (l) l
    res


-- not used; symmetric does not make sense here
def rwPairsCuml(mvarId : MVarId)(symm: Bool) :  List Expr  → MetaM (List Expr)  := 
        fun l  =>
          do
            let step ← rwPairs mvarId symm l l
            return step ++ l 

-- not used; symmetric does not make sense here
def iterRWPairsM(n : Nat)(mvarId : MVarId)(symm: Bool) : List Expr → MetaM (List Expr) :=
  match n with
  | 0 => fun l => return l
  | m + 1 => fun l => do
       let prev ← iterRWPairsM m mvarId symm  l
       return ← rwPairsCuml mvarId symm prev

def iterAppRWM(n: Nat)(mvarId : MVarId) : List Expr → MetaM (List Expr) :=
   match n with
  | 0 => fun l => return l
  | m + 1 => fun l => do
       let prev ← iterAppRWM m mvarId  l
       let eqs ←  prev.filterM (fun e => do (← inferType e).isEq)
       let rwStep ← rwPairs mvarId false prev eqs
       let rwFlipStep ←  rwPairs mvarId true prev eqs
       let appStep ← applyPairsMeta prev
       return (rwStep.append (rwFlipStep.append appStep))



def iterAppRWDirect(n: Nat)(mvarId : MVarId) : Array Expr → TermElabM (Array Expr) :=
   match n with
  | 0 => fun l => return l
  | m + 1 => fun l => do
      let prev ←  iterAppRWDirect m mvarId  l
      let rwStep ←  rwAppCongStep mvarId prev
      return rwStep

def iterAppRWMDirect(n: Nat)(mvarId : MVarId) : List Expr → MetaM (List Expr) :=
  fun l => ((iterAppRWDirect n mvarId l.toArray).run').map (Array.toList)


def propagateEqualitiesOld (eqs: Array Expr) : TermElabM (Array Expr) := 
  do
    let mut eqsymm : Array Expr := #[]
    for eq in eqs do
      let type ← inferType eq
      if type.isEq then
        unless eqsymm.contains eq do
          eqsymm ← eqsymm.push eq
        let seq ← whnf (← mkAppM `Eq.symm #[eq])
        unless eqsymm.contains seq do
          eqsymm ← eqsymm.push seq
    let mut withLhs : HashMap Expr (Array Expr) := HashMap.empty
    let mut withRhs : HashMap Expr (Array Expr) := HashMap.empty
    -- logInfo m!"eqsymm: {eqsymm.size}"
    for eq in eqsymm do
      let type ← inferType eq
      match type.eq? with
      | none => ()
      | some (α , lhs, rhs) =>
        let lhsUp := 
          match withLhs.getOp lhs with
          | some arr => arr.push eq
          | none => #[eq] 
        withLhs ← withLhs.insert lhs lhsUp
        let rhsUp := 
          match withRhs.getOp rhs with
          | some arr => arr.push eq
          | none => #[eq] 
        withRhs ← withRhs.insert rhs rhsUp
    -- logInfo m!"withLhs: {withLhs.size}"
    -- logInfo m!"withRhs: {withRhs.size}"
    let mut  accum := eqsymm
    for (k, eqs1) in withRhs.toArray do
      let eqs2 := (withLhs.find? k).getD #[]
      for eq1 in eqs1 do
        for eq2 in eqs2 do
          accum ← accum.push (← mkAppM `Eq.trans #[eq1, eq2])
    return accum

def propagateEqualitiesTask (eqs: Array Expr) : TermElabM (Array Expr) := 
  do
    let mut eqsymm : Array Expr := #[]
    for eq in eqs do
      let type ← inferType eq
      if type.isEq then
        unless eqsymm.contains eq do
          eqsymm ← eqsymm.push eq
        let seq ← whnf (← mkAppM `Eq.symm #[eq])
        unless eqsymm.contains seq do
          eqsymm ← eqsymm.push seq
    let mut withLhs : HashMap Expr (Array Expr) := HashMap.empty
    let mut withRhs : HashMap Expr (Array Expr) := HashMap.empty
    -- logInfo m!"eqsymm: {eqsymm.size}"
    for eq in eqsymm do
      let type ← inferType eq
      match type.eq? with
      | none => ()
      | some (α , lhs, rhs) =>
        let lhsUp := 
          match withLhs.getOp lhs with
          | some arr => arr.push eq
          | none => #[eq] 
        withLhs ← withLhs.insert lhs lhsUp
        let rhsUp := 
          match withRhs.getOp rhs with
          | some arr => arr.push eq
          | none => #[eq] 
        withRhs ← withRhs.insert rhs rhsUp
    -- logInfo m!"withLhs: {withLhs.size}"
    -- logInfo m!"withRhs: {withRhs.size}"
    let mut  accum := eqsymm
    let ltml : Array (Task (TermElabM (Array Expr))) := 
      withRhs.toArray.map $ fun (k, eqs1) => 
        Task.spawn $ fun _ => do
          let eqs2 := (withLhs.find? k).getD #[]
          eqs2.concatMapM $ fun eq2 => do
            eqs1.mapM $ fun eq1 => mkAppM `Eq.trans #[eq1, eq2]
    let tlml := Task.array ltml 
    let tml := tlml.map $ fun lst => 
      (Array.inTermElab lst).map (fun ll => (Array.join ll))
    tml.get
