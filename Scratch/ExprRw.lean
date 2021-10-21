import Scratch.ExprAppl
import Lean.Meta
import Lean.Elab
open Lean
open Meta
open Elab
open Lean.Elab.Tactic

def rwPushEq  (mvarId : MVarId) (e : Expr) (heq : Expr) 
      (symm : Bool := false): MetaM (Expr × Nat) :=
  do
    let t ← inferType e
    let rwr ← Meta.rewrite mvarId t heq symm
    let pf := rwr.eqProof
    let tt := rwr.eNew
    let pushed ← mkAppM `Eq.mp #[pf, e]
    return (pushed, rwr.mvarIds.length)

def eqCongrOpt (f: Expr)(eq : Expr) : MetaM (Option Expr) :=
  do
    try
      let res ← mkAppM ``congrArg #[f, eq]
      return some res
    catch e => 
      return none 

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
      do
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
    do
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

def iterAppRWMTask(n: Nat)(mvarId : MVarId) : List Expr → Task (MetaM (List Expr)) :=
   match n with
  | 0 => fun l => Task.pure $ return l
  | m + 1 => fun l => do
      let prevTask := iterAppRWMTask m mvarId  l
      prevTask.bind $ fun prevM =>
        let step : MetaM (Task (MetaM (List Expr))) := prevM.bind $ 
          fun prev => 
            do 
            let eqs ←  prev.filterM (fun e => do  (← inferType e).isEq)
            let rwStepTask := rwPairsTask mvarId false prev eqs
            let rwFlipStepTask := rwPairsTask mvarId true prev eqs
            let appStepTask := applyPairsMetaTask prev
            let triple := rwStepTask.join (rwFlipStepTask.join appStepTask)
            let combine : Task (MetaM (List Expr)) := triple.map $ fun (rwStep, rwFlipStep, appStep) =>
              do
                let step := (← rwStep) ++ (← rwFlipStep) ++ (← appStep)
                return step
            return combine
        Task.pure (return [])
  where
    metaMerge : MetaM (List Expr) → MetaM (List Expr) → MetaM (List Expr) := fun m1 m2 =>
      do
        let m1 := (← m1)
        let m2 := (← m2)
        return m1 ++ m2
    taskMetaMerge : Task (MetaM (List Expr)) → Task (MetaM (List Expr)) → 
      Task (MetaM (List Expr)) := fun m1 m2 =>
        (m1.join m2).map $ fun (m1, m2) => metaMerge m1 m2
    stepTask : List Expr → Task (MetaM (List Expr)) :=
      sorry