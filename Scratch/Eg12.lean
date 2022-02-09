import Lean.Meta 
import Lean.Elab
open Lean Meta Elab Term

declare_syntax_cat number

syntax "one" : number
syntax "two" : number
syntax num : number

def value : Syntax → MetaM Nat
| `(number|one) => return 1
| `(number|two) => return 2
| `(number|$n:numLit) => return (Syntax.isNatLit? n).get!
| _ => throwIllFormedSyntax

syntax (name:= adder) "add" number "to" number : term
@[termElab adder] def addedImp : TermElab :=
  fun stx _ =>
    match stx with
    | `(add $s:number to $t:number) => do
      let x ← value s
      let y← value t
      return ToExpr.toExpr (x + y)
    | _ => throwIllFormedSyntax  

#check add one to two

#eval add one to 7

syntax (name:=isType) "type?" term : term
@[termElab isType] def isTypeImpl : TermElab := fun stx _ => 
  match stx with
  | `(type? $s) => do
        let x ← elabTerm s none true true
        let check := (← inferType x).isSort
        if check then return mkConst `Bool.true else return mkConst `Bool.false
  | _ => throwIllFormedSyntax

#eval type? Nat
#eval type? 3
#eval type? 1 = 2

syntax (name:=isProof) "proof?" term : term
@[termElab isProof] def isProofImpl : TermElab := fun stx _ => 
  match stx with
  | `(proof? $s) => do
        let x ← elabTerm s none true true
        let check := (← inferType (← inferType x)).isProp
        if check then return mkConst `Bool.true else return mkConst `Bool.false
  | _ => throwIllFormedSyntax

#eval proof? 1 = 1
#eval proof? (rfl : 1 = 1)

syntax (name:=getDom) "dom!" term : term
@[termElab getDom] def getDomImpl : TermElab := fun stx _ => 
  match stx with
  | `(dom! $s) => do
        let x ← elabTerm s none true true
        Term.synthesizeSyntheticMVarsNoPostponing 
        match x with
        | Expr.forallE _ t b .. =>
            logInfo m!"body: {b}" 
            return t
        | Expr.lam _ t b .. => 
            logInfo m!"body: {b}" 
            return t
        | Expr.letE _ t v b .. =>
            logInfo m!"expr: {x}"
            logInfo m!"body: {b}"
            logInfo m!"value: {v}" 
            return t
        | _ => throwError m!"domain does not make sense for {x}"
  | _ => throwIllFormedSyntax

#check dom! ((x: Nat) →  x = 1)

#check dom! (fun (x: Nat) => x + 1)

#check fun y => dom! (let (x: Nat) := y + 2; x + 3)

open Nat

def factorial: Nat→ Nat
| 0 => 1
| n + 1 => (n + 1) * factorial n

def idnt (α : Type)(a: α) : α := a

#eval idnt _ 1
#eval idnt Nat 2

def oneDigit (n: Nat)(pf: n < 10): Nat := n

#eval oneDigit 3 (by skip; apply Nat.succ_lt_succ; apply Nat.succ_lt_succ; apply Nat.succ_lt_succ;    exact Nat.zero_lt_succ 6)

#eval oneDigit 3 (Nat.succ_lt_succ (Nat.succ_lt_succ ((Nat.succ_lt_succ (Nat.zero_lt_succ _)))))

#check Nat.zero_lt_succ 

partial def gcd0(a b: Nat): Nat :=
  if b = 0 then a else 
  if b < a then gcd b (a % b) else gcd (b % a) a

def gcd1(n: Nat)(a b: Nat)(wa: a ≤ n)(wb: b ≤ n): Nat := sorry

#eval gcd0 12 16

#check TermElabM.run' _ _

def toMeta{α : Type}(x: TermElabM α) : MetaM α := 
  x.run' 