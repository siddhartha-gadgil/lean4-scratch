import Scratch.ExprAppl
import Lean.Meta
import Lean.Elab
import Std.Data.HashMap
open Std
open Lean
open Meta
open Elab
open Lean.Elab.Tactic

def contains : Expr → Expr → MetaM Bool
  | e, x => 
    do 
    if ← isDefEq e x then return true
    else 
    match e with
    | Expr.app f a _ => (← contains f x) || (← contains a x)
    | Expr.lam _ _ b _ => (← contains b x)
    | Expr.forallE _ _ b _ => (← contains b x) 
    | _ => return false


-- copied from lean4 source code
def rewriteProof (e: Expr) (heq : Expr) (symm : Bool := false) : MetaM (Option Expr) :=
  do
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    match heqType.eq? with
    | none => none
    | some (α , lhs, rhs) =>
    let heqType := if symm then ← mkEq rhs lhs else heqType
    let hep := if symm then mkEqSymm heq else heq
    if lhs.getAppFn.isMVar then none
    else
    let e ← instantiateMVars e
    let eAbst ←  kabstract e lhs
    if !eAbst.hasLooseBVars then none
    else
    let eNew := eAbst.instantiate1 rhs
    let eNew ← instantiateMVars eNew
    let eEqE ← mkEq e e
    let eEqEAbst := mkApp eEqE.appFn! eAbst
    let motive := Lean.mkLambda `_a BinderInfo.default α eEqEAbst
    if !(← isTypeCorrect motive) then none
    else            
    let eqRefl ← mkEqRefl e
    let eqPrf ← mkEqNDRec motive eqRefl heq
    return some eqPrf

def rwPushOpt(e : Expr) (heq : Expr) 
      (symm : Bool := false): MetaM (Option Expr) :=
  do
    let t ← inferType e
    let pfOpt ← rewriteProof t heq symm
    match pfOpt with
    | none => return none
    | some pf =>
      try
        let expr ← mkAppM ``Eq.mp #[pf, e]
        let exprType ← inferType expr
        if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  
        then return some expr
        else return none
      catch _ => 
        return none

def rwPushEq  (mvarId : MVarId) (e : Expr) (heq : Expr) 
      (symm : Bool := false): MetaM (Expr × Nat) :=
  do
    let t ← inferType e
    let rwr ← Meta.rewrite mvarId t heq symm
    let pf := rwr.eqProof
    -- let tt := rwr.eNew
    let pushed ← mkAppM `Eq.mp #[pf, e]
    return (pushed, rwr.mvarIds.length)

def eqCongrOpt (f: Expr)(eq : Expr) : MetaM (Option Expr) :=
  do
    try
      let expr ← mkAppM ``congrArg #[f, eq]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then return some expr
      else 
        return none
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

def isle (type: Expr)(evolve : Array Expr → TermElabM (Array Expr))(init : List Expr)
       (includePi : Bool := true): TermElabM (Array Expr) := 
    withLocalDecl Name.anonymous BinderInfo.default (type)  $ fun x => 
        do
          let l := x :: init
          -- logInfo m!"initial in isle: {l}"
          let evb ← evolve l.toArray
          let evc ← evolve init.toArray
          let mut evl : Array Expr := #[]
          for y in evb do
            unless (evc.contains y) do 
              evl := evl.push y 
          let evt ← evl.filterM (fun x => liftMetaM (isType x))
          let exported ← evl.mapM (fun e => mkLambdaFVars #[x] e)
          let exportedPi ← evt.mapM (fun e => mkForallFVars #[x] e)
          let res := if includePi then exported ++ exportedPi else exported
          return res

def isleSum (types: List Expr)(evolve : Array Expr → TermElabM (Array Expr))(init : List Expr) : 
        TermElabM (Array Expr) := 
        match types with
        | [] => return #[]
        | h :: t => 
          do
            let tail ← isleSum t evolve init
            let head ← isle h evolve init
            return head ++ tail        

def Array.join {α : Type}[BEq α](a : Array (Array α)) : Array α := do
  let mut res : Array α  := #[]
  for x in a do
    for y in x do
      res := if res.contains y then res else res.push y
  return res

def eqIsles (eqs: Array Expr)(evolve : Array Expr → TermElabM (Array Expr))(init : List Expr) : 
        TermElabM (Array Expr) := 
        do
        let res ← eqs.filterMapM $ fun eq => do
          match (← inferType eq).eq? with
          | some (α, lhs, rhs) => 
            do
              Elab.logInfo m!"isles for: {α}; {lhs} = {rhs}"
              let fs ← isle α evolve init
              -- Elab.logInfo m!"generated in isle: {← fs.mapM (fun e => whnf e)}"
              -- Elab.logInfo m!"types from  isle: {← fs.mapM (fun e => do whnf (← inferType e))}"
              let shifted ← fs.filterMapM (fun f => eqCongrOpt f eq)
              -- logInfo m!"example: {← mkAppM ``congrArg #[fs[0], eq]}"
              -- Elab.logInfo m!"shifted by isle: {shifted}"
              return some shifted
          | _ => return none
        return res.join

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

def List.inTermElab {α : Type}(l : List (TermElabM α)) : TermElabM (List α) :=
  l.foldl (fun ysM xM =>
            do 
              return (← xM) :: (← ysM)) (return [])

def Array.inTermElab {α : Type}(l : Array (TermElabM α)) : TermElabM (Array α) :=
  l.foldl (fun ysM xM =>
            do 
              return (← ysM).push (← xM)) (return #[])


#check @Array.foldl

  

def rwAppCongStepTask : Array Expr → Array Name → Task (TermElabM (Array Expr)):=
    fun l names =>
    let ltml :=
      l.map $ fun arg => 
      Task.spawn $ fun _ =>
      do
        let type ← inferType arg
        if type.isEq
        then 
          let rws ← l.filterMapM (fun f => rwPushOpt  f arg)
          let rwsFlip ← l.filterMapM (fun f => rwPushOpt f arg true)
          let congs ← l.filterMapM (fun f => eqCongrOpt f arg)
          let apps ← l.filterMapM (fun f => applyOptM f arg)
          let nameApps ← names.filterMapM (fun name => nameApplyOptM name arg)
          return (rws.append 
                    (rwsFlip.append (congs.append (apps)))).append (nameApps) 
        else 
          let apps ← l.filterMapM (fun f => applyOptM f arg)
          let nameApps ← names.filterMapM (fun name => nameApplyOptM name arg)
          let nameAppPairsRaw ← 
            Array.inTermElab (l.map (fun arg2 => names.filterMapM (fun name => 
                    nameApplyPairOptM name arg arg2
                    )))
          let nameAppPairs := nameAppPairsRaw.join
          return apps ++ nameApps ++ nameAppPairs
    let tlml := Task.array ltml 
    let tml := tlml.map $ fun lst => 
      (Array.inTermElab lst).map (fun ll => (Array.join ll) ++ l)
    tml

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

def appStepTask : Array Expr → Task (TermElabM (Array Expr)):=
    fun l =>
    let ltml :=
      l.map $ fun arg => 
      Task.spawn $ fun _ =>
      do
        let apps ← l.filterMapM (fun f => applyOptM f arg)
        return apps
    let tlml := Task.array ltml 
    let tml := tlml.map $ fun lst => 
      (Array.inTermElab lst).map (fun ll => (Array.join ll) ++ l)
    tml

def iterAppRWTask(n: Nat) : Array Expr → Array Name  → TermElabM (Array Expr) :=
   match n with
  | 0 => fun l _ => return l
  | m + 1 => fun l names => do
      let prev ←  iterAppRWTask m   l names
      let rwStepTask := rwAppCongStepTask  prev names
      let isles ← eqIsles prev 
        (fun list => (iterAppRWTask m list names)) prev.toList
      -- Elab.logInfo m!"isles: {isles}"
      let rwStep ← rwStepTask.get
      return rwStep ++ isles

def iterAppRWMTask(n: Nat): List Expr → List Name → TermElabM (List Expr) :=
  fun l names => ((iterAppRWTask n l.toArray names.toArray)).map (Array.toList)

def iterAppTask(n: Nat) : Array Expr → TermElabM (Array Expr) :=
   match n with
  | 0 => fun l => return l
  | m + 1 => fun l => do
      let prev ←  iterAppTask m   l
      let stepTask := appStepTask prev
      let step ← stepTask.get
      return step

def iterAppMTask(n: Nat) : List Expr → TermElabM (List Expr) :=
  fun l => ((iterAppTask n  l.toArray)).map (Array.toList)

def iterAppRWDirect(n: Nat)(mvarId : MVarId) : Array Expr → TermElabM (Array Expr) :=
   match n with
  | 0 => fun l => return l
  | m + 1 => fun l => do
      let prev ←  iterAppRWDirect m mvarId  l
      let rwStep ←  rwAppCongStep mvarId prev
      return rwStep

def iterAppRWMDirect(n: Nat)(mvarId : MVarId) : List Expr → MetaM (List Expr) :=
  fun l => ((iterAppRWDirect n mvarId l.toArray).run').map (Array.toList)

  initialize exprArrCache : IO.Ref (HashMap Name (Array Expr)) ← IO.mkRef (HashMap.empty)

def getArrCached? (name : Name) : IO (Option (Array Expr)) := do
  let cache ← exprArrCache.get
  return (cache.find? name)

def cacheArr (name: Name)(e: Array Expr)  : IO Unit := do
  let cache ← exprArrCache.get
  exprArrCache.set (cache.insert name e)
  return ()

def saveExprArr (name: Name)(es: Array Expr) : TermElabM (Unit) := do
  let es ← es.mapM (fun e => whnf e)
  Term.synthesizeSyntheticMVarsNoPostponing 
  let espair ← es.mapM (fun e => do Term.levelMVarToParam (← instantiateMVars e))
  let es ← espair.mapM fun (e, _) => return e
  cacheArr name es
  return ()

def loadExprArr (name: Name) : TermElabM (Array Expr) := do
  let cache ← exprArrCache.get
  match cache.find? name with
  | some es => return es
  | none => throwError m!"no cached expr for {name}"
