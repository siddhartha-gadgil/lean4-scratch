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
        match x with
        | Expr.forallE _ t b .. =>
            logInfo m!"body: {b}" 
            return t
        | Expr.lam _ t b .. => 
            logInfo m!"body: {b}" 
            return t
        | _ => throwError m!"domain does not make sense for {x}"
  | _ => throwIllFormedSyntax

#check dom! ((x: Nat) →  x = 1)

#check dom! (fun (x: Nat) => x + 1)