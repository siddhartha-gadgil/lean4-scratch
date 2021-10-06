import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean
open Nat 

inductive TermSeq where
  | empty : TermSeq
  | cons : {α : Type} → (a : α) → (tail: TermSeq) → TermSeq



syntax (name:= termseq) "#⟨" term,* "⟩" : term
-- macro_rules
--   | `( #⟨$[$xs:term],*⟩ ) => 
--     xs.foldr (fun head accum => 
--       do 
--         let tail ← accum
--         return ← `(TermSeq.cons $head $tail)) `(TermSeq.empty)

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

partial def decomposeSeq : Expr → MetaM (List Expr) :=
  fun expr => 
  do 
    let mvar ←  mkFreshExprMVar none
    let tmvar ← mkFreshExprMVar (mkConst `TermSeq)
    let sExp ←  mkAppM ``TermSeq.cons #[mvar, tmvar]
    if ← isDefEq sExp expr then
      let prev ← decomposeSeq tmvar
      return mvar :: prev
    else 
      return []

partial def seqLength : Expr → MetaM Nat := fun expr =>
  do
    let l ← decomposeSeq expr
    return l.length

syntax (name:= tsl) "tsl!" term : term 

@[termElab tsl] def tslImpl : TermElab :=
  fun stx expectedType? =>
    match stx with
    | `(tsl!%$tk $s) =>
      do 
        let e ← elabTerm s none
        let l ← seqLength e
        Lean.Elab.logInfoAt tk m!"expr: {(← e)}"
        Lean.Elab.logInfoAt tk m!"whnf: {(← whnf e)}"
        Lean.Elab.logInfoAt tk m!"length: {(← l)}"
        return ← ToExpr.toExpr l 
    | _ => Elab.throwIllFormedSyntax



def ts := TermSeq.cons 3 TermSeq.empty

#eval tsl! ts
#eval tsl! #⟨3, 4, "this"⟩

#check  #⟨3, 4, "this"⟩
#check fun x: Nat => #⟨x, x, "this", 4⟩

example : (fun x: Nat => #⟨x, x, "this", 4⟩) 3 = #⟨3, 3, "this", 4⟩ := rfl

open Lean.Elab.Tactic

syntax (name:= blah) "blah" : tactic
@[tactic blah] def blahImpl : Tactic :=
  fun stx =>
    do
      Lean.Elab.logInfo "blah say I"
      return ()

syntax (name := tsltac) "tslength" term : tactic
@[tactic tsltac] def tslTacImpl : Tactic := 
  fun stx =>
    match stx with
    | `(tactic|tslength $s) =>
      do
        let mvar ← getMainGoal
        let e ← liftM (Elab.Term.elabTerm s none true true)
        let l ← seqLength e
        let n := ToExpr.toExpr l 
        replaceMainGoal []
        assignExprMVar mvar n
    | _ => Elab.throwIllFormedSyntax

def tstacEg : Nat := by 
        blah
        tslength #⟨3, 4, "this"⟩

#eval tstacEg

universe u v

def factorThrough(α : Sort u) (β : Sort v)(b : β ) : (β  → α ) → α   := 
    fun g => g b

syntax (name:= useterm) "use" term ("with" term)? "as" ident : tactic
@[tactic useterm] def usetermImpl : Tactic :=
   fun stx =>
    match stx with
    | `(tactic|use $s with $t as $n) =>
    do
      let mvar ← getMainGoal
      let name ← n.getId
      let typ ← liftM (Elab.Term.elabTerm t none true true)
      let value ← liftM (Elab.Term.elabTerm s (some typ) true true)
      let target ← getMVarType mvar
      let exp ← mkAppM `factorThrough #[target, typ, value]
      Lean.Elab.logInfo m!"can use {value} : {typ} for target: {(← target)}"
      liftMetaTactic $ fun m => 
      (do
        let appGoalList ←  apply mvar exp
        let appGoal := appGoalList.head!
        let ⟨_, introGoal⟩ ←  intro appGoal name  
        return [introGoal])
    | `(tactic|use $s as $n) =>
    do
      let mvar ← getMainGoal
      let name ← n.getId
      let value ← liftM (Elab.Term.elabTerm s none true true)
      let typ ← inferType value
      let target ← getMVarType mvar
      let exp ← mkAppM `factorThrough #[target, typ, value]
      Lean.Elab.logInfo m!"can use {value} : {typ} for target: {(← target)}"
      liftMetaTactic $ fun m => 
      (do
        let appGoalList ←  apply mvar exp
        let appGoal := appGoalList.head!
        let ⟨_, introGoal⟩ ←  intro appGoal name  
        return [introGoal])
    | _ => Elab.throwIllFormedSyntax

example : Nat := by
        use 3 with Nat as n
        use "this" as s
        let x := 3
        have b := "d"
        exact n

syntax (name:= dupllet) "assign" ident "::" term "as" term : tactic
@[tactic dupllet] def assignImpl : Tactic :=
  fun stx =>
    match stx with
    | `(tactic|assign $n:ident :: $t as  $i) => 
      do
        let name ← n.getId
        let typ ← liftM (Elab.Term.elabTerm t none true true)
        let value ← liftM (Elab.Term.elabTerm i (some typ) true true)
        let mvar ← getMainGoal
        withMVarContext mvar do
          let mvar2 ← mkFreshExprMVar (← getMVarType mvar) 
          let mvarId2 := mvar2.mvarId!
          replaceMainGoal [mvarId2]
          withLetDecl  name  typ value $ fun x =>
            do          
            assignExprMVar mvar (← mkLetFVars #[x] mvar2)          
            return ()  
    | _ => Elab.throwIllFormedSyntax

def fl := 4.5
def three := 3

def letTac : Nat   := by
        let p := 3
        assign y :: Nat as 3
        exact p
        done
        

#eval tsl! #⟨three, fl, "this"⟩

def getFloat (s: String) : Option Float :=
  (Syntax.decodeScientificLitVal? s).map (fun ⟨m, s, e⟩ => Float.ofScientific m s e) 

#eval getFloat "3.1415"

#eval Syntax.decodeScientificLitVal? (Float.toString (3.145))

-- copied from @Mac's code below and modified
def parseOpt (s : String) : Option Float :=
  match Json.Parser.num s.mkIterator with
  | Parsec.ParseResult.success _ res =>
    some <| Float.ofInt res.mantissa * 10 ^ - Float.ofNat res.exponent
  | Parsec.ParseResult.error it err  => none

def parseGet (s : String) : Nat ×  Nat :=
  match Json.Parser.num s.mkIterator with
  | Parsec.ParseResult.success _ res =>
      (res.mantissa.toNat, res.exponent)
  | Parsec.ParseResult.error it err  => (0, 0)


syntax (name:= floatlit) "float!" term : term

@[termElab floatlit] def floatlitImpl : TermElab :=
    fun stx expectedType? =>
      match stx with
      | `(float! $s) =>
        do  
           let fl ← Elab.Term.elabTerm s (some (Lean.mkConst `Float))
           let strRaw ← mkAppM ``Float.toString #[fl] 
           let str ← whnf strRaw
          --  let ⟨n, _, _⟩ := (Syntax.isScientificLit? s).get! 
           return ← mkAppM ``parseGet #[str]  
          --  return  ToExpr.toExpr n
      | _ => Elab.throwIllFormedSyntax

def pi := 3.1415

#eval float! 3.14
#eval float! pi
#eval float! (3.1 * 6)

syntax ident ("⌣" ident)? "↦" term : term

macro_rules
  | `( $x:ident ↦ $y:term ) => `(fun $x => $y)
  | `( $x:ident ⌣ $t: ident ↦ $y:term ) => `(fun ($x : $t) => $y)  

def mapfn : Nat → Nat := n ↦ n + 1

def mapFn2 := k ⌣ Nat ↦ (k + 1) 

-- copied from Zulip chat due to @mac 

-- import Lean.Data.Json.Parser

def parse (s : String) : Except String Float :=
  match Json.Parser.num s.mkIterator with
  | Parsec.ParseResult.success _ res =>
    Except.ok <| Float.ofInt res.mantissa * 10 ^ - Float.ofNat res.exponent
  | Parsec.ParseResult.error it err  => Except.error s!"offset {it.i.repr}: {err}"

#eval parse "1.3" -- Except.ok 1.300000


def th3:= Thunk.mk (fun () => 3)

def addN (n : Nat) : Thunk Nat →  Thunk Nat :=
      let succT : Nat → Thunk Nat := fun n => Thunk.mk (fun () => n + 1)
      match n with
      | 0 => id
      | k + 1 => fun tn => (addN k tn).bind succT

#reduce (addN 20) th3

-- credit: 
-- https://www.classes.cs.uchicago.edu/archive/2019/spring/22300-1/lectures/LazyLists/index.html

mutual
  inductive LazyList (α : Type) where
  | mk : Thunk (LazyListCell α) → LazyList α

  inductive LazyListCell (α : Type) where
  | nil : LazyListCell α
  | cons : α → LazyList α → LazyListCell α
end