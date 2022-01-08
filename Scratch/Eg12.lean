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