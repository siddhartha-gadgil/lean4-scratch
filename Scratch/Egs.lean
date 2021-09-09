import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

def lower (n : MetaM Nat) : CoreM Nat :=
  n.run' {}

def raise (n: CoreM Nat) : MetaM Nat :=
  do 
    let i <- n
    return i

-- copied from source

syntax (name := fooKind) "foo!" term : term

@[termElab fooKind] def elabFoo : TermElab :=
fun stx expectedType? => elabTerm (stx.getArg 1) expectedType?

#check foo! 10

def eg1 : Bool := foo! true

-- example of how to use the elaborator

syntax (name := addone) "addone!" (term)? : term

@[termElab addone] def addoneImpl : TermElab :=
fun stx expectedType? =>
  match stx with
  | `(addone! $s) => 
    do
      let s0 ← s
      let expr0 ←  elabTerm s0 (some (Lean.mkConst `Nat)) 
      let name2 : Name := `Nat.succ
      let expr : Expr ←  
        mkAppM name2  #[expr0] 
            -- the expression returned by a function
      return expr
  | _ =>
    do
      let name : Name := `Nat.zero
      let name2 : Name := `Nat.succ
      let expr : Expr :=  
        mkApp (Lean.mkConst name2)  (Lean.mkConst name) 
            -- the expression returned by a function
      return expr

def eg2 := addone! 10

#eval eg2
#eval 3 + addone!

def metaAddOne (n: MetaM Nat) : MetaM Nat :=
  do
    let i <- n
    return i + 1

def addOne(n: Nat) : Nat := addone! n
  
#print addOne
#eval addOne 7

syntax (name := tryapp) term " >>> " term : term

def hasType (exp: Expr) : TermElabM Bool :=
  do
    try
      let typ  ← inferType exp
      return true
    catch _ => 
      return false

@[termElab tryapp] def tryappImpl : TermElab :=
fun stx expectedType? =>
  match stx with
  | `($s >>> $t) =>
    do
      let f <- elabTerm s none
      let x <- elabTerm t none
      let expr : Expr := mkApp f x
      let c  ← isTypeCorrect expr
      let cc ← hasType expr 
      if c  then
        return expr
      else
        return (Lean.mkConst `Nat.zero)
  | _ => 
    do 
      return (Lean.mkConst `none) 


set_option pp.raw true
set_option pp.raw.maxDepth 10


inductive Someterm  where
  | something  : {α : Type} → (a: α ) → Someterm
  | nothing : Someterm

def Someterm.isEmpty : Someterm → Bool 
  | Someterm.something  _ => false
  | Someterm.nothing => true

syntax (name := tryapp2) term " >>>> " term : term

@[termElab tryapp2] def tryappImpl2 : TermElab :=
  let nt := Lean.mkConst `Someterm.nothing
  let st := Lean.mkConst `Someterm.something
  
  fun stx expectedType? =>
    match stx with
    | `($s >>>> $t) =>
      do
        let f <- elabTerm s none
        let x <- elabTerm t none
        let expr : Expr ←  mkApp f x
        let c ←  isTypeCorrect expr
        -- let cc := !expr.hasExprMVar
        if c then
          return Lean.mkApp st expr
        else
          return nt
    | _ => 
      do 
        return nt

#check Nat.succ >>>> 3
#check Nat.succ >>>> true


#check (Eq.trans >>>> (rfl : Nat.zero = Nat.zero))        

def optApp {α β γ : Type} (f : α → β) (x : γ)  :=
  f >>>> x

#print optApp

def eg3 := optApp Nat.succ 3

def eg4 := optApp Nat.succ true

#eval eg3.isEmpty -- this fails, the lambda body does not type check
#eval eg4.isEmpty

#print eg3

def exprApp (e1 e1t e2 : Expr) : MetaM Expr :=
  let n := Name.mkSimple "unsafe-name"
  withLetDecl n e1t e1 fun x => do
    let b ←  (mkAppM n #[e2])
    return ← (mkLetFVars #[x] b)

syntax (name := unapp) term " :: " term " |< " term : term

@[termElab unapp] def unappImpl : TermElab :=
  let nt := Lean.mkConst `Someterm.nothing
  let st := Lean.mkConst `Someterm.something  
  let n := Name.mkSimple "unsafe-name"
  fun stx expectedType? =>
    match stx with
    | `($s :: $t |< $u) =>
      do
        let f <- elabTerm s none
        let type ← elabTerm t none
        let z <- elabTerm u none
        let expr : Expr ←  withLetDecl n type f fun x => do
                              let b ←  (mkAppM n #[z])
                              return ← (mkLetFVars #[x] b)
        let c <- isTypeCorrect expr
        if c then
          return Lean.mkApp st expr
        else
          return nt
    | _ => 
      do 
        return nt

-- #check Nat.succ :: (Nat → Nat) |< 3



#print unappImpl
#print exprApp

syntax (name := minlet) "minlet!" : term

@[termElab minlet] def minletImpl : TermElab :=
  fun stx expectedType? =>
  let n := Name.mkSimple "n"
  let z := Lean.mkConst `Nat.zero
  let ty := Lean.mkConst `Nat
  withLetDecl n ty z fun x => do
    let e <- mkLetFVars #[x] x
    return e

#print minletImpl  
#check minlet!

def blah := Meta.isExprDefEqAux

def nameLess (name: Name) := 1

syntax (name := ignorename) "ignore!" ident : term

macro_rules
  | `(ignore! $s) => `(nameLess `$s)

#check nameLess ``Nat.succ

inductive WrapTerm where
  | wrap : {α : Type} → (a: α ) → WrapTerm
  | wrapName : Name → WrapTerm
  | wrapExpr : Array Expr → WrapTerm

#check WrapTerm

def makeTypeFamily := Eq 1
      
#check makeTypeFamily
#check Eq

def makeProp : Prop := by
  apply Eq
  focus
    exact 1
  exact 2 

def makeType : Type := by
  apply Option
  exact Nat
  

def asFunc {α β : Type} (a: α) : (α → β) → β  := 
    fun f => f a

def asPi {α : Type}{motive : α → Type} (a: α) : 
      ((x : α) → motive x) → motive a :=
        fun f => f a    

def natGen : Nat := by
    apply (asFunc 3)
    exact Nat.succ
