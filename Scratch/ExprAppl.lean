import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean
open ToExpr

#eval true && false

def applyOptM (f x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← elabAppArgs f #[] #[Arg.expr x] none (explicit := false) (ellipsis := false)
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then return some expr
      else return none
    catch e =>
      return none

def nameApplyOptM (f: Name) (x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM f #[x]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then 
        -- Elab.logInfo m!"from name, arg : {expr}"
        return some expr
      else
      Elab.logWarning m!"not type correct : {expr} = {f} ({x})" 
      return none
    catch e =>
        -- Elab.logInfo m!"failed from name, arg : 
        --     {f} at {x} with type {← inferType x}"
      return none

def nameApplyPairOptM (f: Name) (x y: Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← mkAppM f #[x, y]
      let exprType ← inferType expr
      if (← isTypeCorrect expr) &&  (← isTypeCorrect exprType)  then 
        -- Elab.logInfo m!"from name, arg : {expr}"
        return some expr
      else
      Elab.logWarning m!"not type correct : {expr} = {f}({x}, {y})" 
      return none
    catch e =>
        -- Elab.logInfo m!"failed from name, arg : 
        --     {f} at {x}, {y} with type {← inferType x}"
      return none

syntax (name:= nameapp) "nameapply!" ident "at" term ("with" term)? : term 
@[termElab nameapp] def nameAppImpl : TermElab :=
  fun stx type =>
  match stx with
  | `(nameapply! $n:ident at $t:term) =>
    do
      let f ← n.getId
      let x ← elabTerm t none
      Elab.logInfo m!"nameapply! {f} at {x}"
      let exp ← mkAppM f #[x]
      return exp
  | `(nameapply! $n:ident at $t:term with $s:term) =>
    do
      let f ← n.getId
      let x ← elabTerm t none
      let y ← elabTerm s none
      Elab.logInfo m!"nameapply! {f} at {x}, {y}"
      let exp ← mkAppM f #[x, y]
      return exp
  | _ => Elab.throwIllFormedSyntax

-- #check fun m: Nat => nameapply! HMul.hMul at m
#eval nameapply! HMul.hMul at (3: Nat) with (4: Nat)

def listAppArgs : Expr → List Expr → TermElabM (List Expr) :=
  fun f args =>
    match args with
    | [] => return []
    | x :: ys => 
      do
        let head ← applyOptM f x
        let tail ← listAppArgs f ys
        match head with
        | some expr => return expr :: tail
        | none => return tail

def Task.join {α β : Type} (t1 : Task α) (t2 : Task β) : Task (α × β) :=
  t1.bind fun a => t2.map fun b => (a, b)

def Task.sequence {α : Type} (ts : List (Task α)) : Task (List α) :=
  ts.foldl (fun t acc => t.bind (fun ys => acc.map (fun x => x :: ys))) (Task.pure [])

def Task.array {α : Type} (ts : Array (Task α)) : Task (Array α) :=
  ts.foldl (fun t acc => t.bind (fun ys => acc.map (fun x => ys.push x))) (Task.pure #[])

def listAppArgsTask : Expr → List Expr → Task (TermElabM (List Expr)) :=
  fun f args =>
    match args with
    | [] => Task.pure (return [])
    | x :: ys => 
      Id.run do
        let headTask := Task.spawn (fun _ => applyOptM f x)
        let tailTask := listAppArgsTask f ys
        headTask.bind $ fun head => 
              tailTask.map $ fun tail =>
                do 
                  let h ← head
                  match h with
                  | some expr => return expr :: (← tail)
                  | none => tail

def applyPairs : List Expr →  List Expr  → TermElabM (List Expr)  := fun l args =>
  match l with
  | [] => return []
  | x :: ys => 
    do
      let head ← listAppArgs x args
      let tail ← applyPairs ys args
      return head ++ tail

-- cumulative and removing duplicates
def applyPairsTask : List Expr →  List Expr  → Task (TermElabM (List Expr))  := 
  fun l args =>
  match l with
  | [] => Task.pure (return [])
  | x :: ys => 
    Id.run do
      let headTask := listAppArgsTask x args
      let tailTask := listAppArgsTask x ys
      headTask.bind $ fun head => 
            tailTask.map $ fun tail =>
              do 
                return ((← head) ++ (← tail) ++ l).eraseDups


def double: Nat→ Nat := fun x => x + x

def expList := [toExpr 1,  toExpr 3, Lean.mkConst `Nat.succ, Lean.mkConst `Nat.zero, 
              Lean.mkConst `double]

def evListEg := applyPairs expList expList

def applyPairsCuml :  List Expr  → TermElabM (List Expr)  := 
        fun l  =>
          do
            let step ← applyPairs l l
            return step ++ l 
            
def applyPairsMeta : List Expr → MetaM (List Expr) :=
  fun l => (applyPairsCuml l).run'

def applyPairsMetaTask : List Expr → Task (MetaM (List Expr)) :=
  fun l => (applyPairsTask l l).map (fun x => x.run')

def iterApplyPairsMeta(n : Nat) : List Expr → MetaM (List Expr) :=
  match n with
  | 0 => fun l => return l
  | m + 1 => fun l => do
       let prev ← iterApplyPairsMeta m l
       return ← applyPairsMeta prev

#eval evListEg
#check evListEg


def typInList? (α : Expr) : List Expr → MetaM (Option Expr) :=
  fun xs =>
    match xs with
    | [] => none
    | x :: xs =>
      do
        let t ← inferType x
        if ← isDefEq t α  then
          return (some x)
        else
          return ← typInList? α xs