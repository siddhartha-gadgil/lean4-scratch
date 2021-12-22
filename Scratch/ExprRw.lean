import Scratch.ExprAppl
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

def whiteListed (n: Name) : TermElabM Bool := do
  let b ← ConstDeps.isWhiteListed (← getEnv) n
  return b


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
       (includePi : Bool := true)(excludeProofs: Bool := false): TermElabM (Array Expr) := 
    withLocalDecl Name.anonymous BinderInfo.default (type)  $ fun x => 
        do
          let l := x :: init
          -- logInfo m!"initial in isle: {l}"
          let evb ← evolve l.toArray
          let evc ← evolve init.toArray
          let mut evl : Array Expr := #[]
          for y in evb do
            unless excludeProofs && ((← inferType y).isProp) do
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

def Array.join {α : Type}[BEq α](a : Array (Array α)) : Array α := Id.run do
  let mut res : Array α  := #[]
  for x in a do
    for y in x do
      res := if res.contains y then res else res.push y
  return res

def eqIsles (eqs: Array Expr)(evolve : Array Expr → TermElabM (Array Expr))(init : List Expr) : 
        TermElabM (Array Expr) := 
        do
        let mut eqGroupMap : HashMap Expr (Array Expr) := HashMap.empty
        for eq in eqs do
          match (← inferType eq).eq? with
          | some (α, lhs, rhs) =>
              let prev := (eqGroupMap.find? α).getD #[] 
              eqGroupMap := eqGroupMap.insert α (prev.push eq)
          | none => ()
        let eqGroups := eqGroupMap.toArray
        let res : Array Expr ← eqGroups.concatMapM $ fun (α, eqns) =>
              do 
              let fs ← isle α evolve init false true
              -- logInfo m!"fs: {fs.size}"
              let shifted ← eqns.concatMapM $ fun eq =>  
                    fs.filterMapM (fun f => eqCongrOpt f eq)
              return shifted
        return res --.join

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

  

def rwAppCongStepTask : Array Expr → Array Name → (TermElabM (Array Expr)):=
    fun l names => 
    let funcs :=  l.filterM $ fun e => 
      let check: TermElabM Bool := do
        let type ← inferType e
        return type.isForall
      check
    let ltml :=
      l.map $ fun arg => 
      Task.spawn $ fun _ =>
      do
        let fns ← funcs
        let apps ← fns.filterMapM (fun f => applyOptM f arg)
        let nameApps ← names.filterMapM (fun name => nameApplyOptM name arg)
        let nameAppPairsRaw ← 
          Array.inTermElab (l.map (fun arg2 => names.filterMapM (fun name => 
                  nameApplyPairOptM name arg arg2
                  )))
        let nameAppPairs := nameAppPairsRaw.join
        let type ← inferType arg
        if type.isEq
        then 
          let rws ← l.filterMapM (fun f => rwPushOpt  f arg)
          let rwsFlip ← l.filterMapM (fun f => rwPushOpt f arg true)
          let congs ← l.filterMapM (fun f => eqCongrOpt f arg)
          return (rws.append 
                    (rwsFlip.append (congs.append (apps)))).append (nameApps) ++ nameAppPairs 
        else           
          return apps ++ nameApps ++ nameAppPairs
    let lst := ltml.map <| fun t=> t.get
    let ml := (Array.inTermElab lst).map (fun ll => (Array.join ll) ++ l)
    ml

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
      let rwStep ← rwStepTask
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
  let lctx ← getLCtx
  let fvarIds ← lctx.getFVarIds
  let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
  let fvars := fvIds.map mkFVar
  Term.synthesizeSyntheticMVarsNoPostponing 
  let espair ← es.mapM (fun e => do Term.levelMVarToParam (← instantiateMVars e))
  let es ← espair.mapM fun (e, _) => return e
  let es ← es.mapM (fun e => mkLambdaFVars fvars e)
  let es ← es.mapM (fun e => whnf e)
  logInfo m!"saving relative to: {fvars}"
  cacheArr name es
  return ()

def loadExprArr (name: Name) : TermElabM (Array Expr) := do
  let lctx ← getLCtx
  let fvarIds ← lctx.getFVarIds
  let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
  let fvars := fvIds.map mkFVar
  logInfo m!"loading relative to: {fvars}"
  let cache ← exprArrCache.get
  match cache.find? name with
  | some es => es.mapM $ fun e => reduce (mkAppN e fvars)
  | none => throwError m!"no cached expr for {name}"

def distinctTypes (exps: Array Expr) : TermElabM (Array Expr) := do
  let mut types : Array Expr := Array.empty
  let mut distinct : Array Expr := Array.empty
  for expr in exps do
    let type ← inferType expr
    unless (types.contains type) do
      types := types.push type
      distinct := distinct.push expr
  return distinct

def propagateEqualities (eqs: Array Expr) : TermElabM (HashMap Expr Expr) := 
  do
    let mut eqsymm : Array Expr := #[]
    let mut eqTypes : HashSet Expr := HashSet.empty
    for eq in eqs do
      let type ← inferType eq
      if type.isEq then
        unless eqTypes.contains type do
          eqsymm := eqsymm.push eq
          eqTypes := eqTypes.insert type
        let seq ← whnf (← mkAppM `Eq.symm #[eq])
        let seqType ← inferType seq
        unless eqTypes.contains seqType do
          eqsymm ← eqsymm.push seq
          eqTypes := eqTypes.insert seqType
    logInfo m!"symmetrize equalities for propagation: {← IO.monoMsNow}"
    logInfo m!"got:{eqsymm.size}"
    let mut withLhs : HashMap Expr (Array (Expr × Expr)) := HashMap.empty
    for eq in eqsymm do
      let type ← inferType eq
      match type.eq? with
      | none => ()
      | some (α , lhs, rhs) =>
        let lhsUp := 
          match withLhs.getOp lhs with
          | some arr => arr.push (eq, rhs)
          | none => #[(eq, rhs)] 
        withLhs ← withLhs.insert lhs lhsUp
    logInfo m!"equality map generated: {← IO.monoMsNow}"
    let mut  accum : HashMap Expr Expr := HashMap.empty
    let mut accumSides : HashSet (Expr × Expr) := HashSet.empty
    for eq1 in eqsymm do
      let type ← inferType eq1
      match type.eq? with
      | none => ()
      | some (α , lhs, rhs) =>
        let eqs2 := (withLhs.getOp rhs).getD #[]
        for (eq2, rhs2) in eqs2 do
        unless (rhs2 == lhs) || (accumSides.contains (lhs, rhs2)) do
          let eq3 ←  mkAppM `Eq.trans #[eq1, eq2]
          let type ← mkEq lhs rhs2
          accum ← accum.insert type eq3
          accumSides := accumSides.insert (lhs, rhs2)
    return accum 


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

def typeVariables (e: Expr) : (List Name) × (List Name) :=
  match e with
  | Expr.forallE n d b c =>
      if c.binderInfo.isExplicit then
        let (l1, l2) := typeVariables b
        (n :: l1, l2)
      else
        let (l1, l2) := typeVariables b
        (l1, n :: l2)
  | _ => ([], [])

syntax(name:= goalVariables) "goalVariables" : tactic 
@[tactic goalVariables] def goalVariablesImp : Tactic :=
  fun stx => 
  withMainContext do
    let (l1, l2) := typeVariables (← getMainTarget)
    logInfo m!"target: {← getMainTarget}"
    logInfo m!"explicit variables: {l1}"
    logInfo m!"implicit variables: {l2}" 
    let lctx ← getLCtx
    let fvarIds ← lctx.getFVarIds
    let fvars := fvarIds.map mkFVar
    logInfo m!"free variables from context: {fvars}"
    logInfo m!"free variable types from context: {← fvars.mapM $ fun x => inferType x}"
    return ()