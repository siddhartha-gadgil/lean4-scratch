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

def fl := 4.5
def three := 3

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
           let fl ← elabTerm s (some (Lean.mkConst `Float))
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

