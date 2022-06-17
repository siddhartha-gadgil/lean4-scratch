import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean
open Nat

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

def addoneMeta (expr0 : Expr) : MetaM Expr := 
    do
      let name2 : Name := `Nat.succ
      let expr : Expr ←  
        mkAppM name2  #[expr0] 
            -- the expression returned by a function
      return expr


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



def metaAddOne (n: MetaM Expr) : MetaM Expr :=
  do
    let i <- n
    let env ← getEnv
    IO.println s!"{env.contains ``succ}"
    IO.println s!"{env.contains `succ}"
    let decls ← getOpenDecls
    IO.println s!"{decls}"
    return mkApp (Lean.mkConst ``succ) i

def addOne(n: Nat) : Nat := addone! n
  
#print addOne
#eval addOne 7
#eval metaAddOne (mkConst `zero)
#eval ``succ

#check Elab.resolveGlobalConstNoOverloadWithInfo 

def egNameM : TermElabM Name := do
  let stx : Syntax ← `(succ)
  IO.println s!"syntax : {stx}"
  match stx with
  | stx@(Syntax.ident _ _ n pre) => IO.println (s!"n: {n};  pre :{pre}")
  | _ => IO.println "Error"
  let ns : List Name ← Lean.resolveGlobalConst stx 
  return ns.head! 

#eval egNameM

#check open List Nat in fun n => cons n

syntax (name := tryapp) term ">>>>>" term : term

@[termElab tryapp] def tryappImpl : TermElab :=
fun stx expectedType? =>
  match stx with
  | `($s >>>>> $t) =>
    do
      let f <- elabTerm s none
      let x <- elabTerm t none
      let expr : Expr := mkApp f x
      let c  ← isTypeCorrect expr
      -- let cc ← hasType expr 
      if c  then
        return expr
      else
        return (Lean.mkConst `Nat.zero)
      -- return (Lean.mkConst `Nat.zero)
  | _ => 
    do 
      return (Lean.mkConst `Nat) 

#check Nat.succ >>>>> Nat.zero
def one := Nat.succ >>>>> Nat.zero
#eval one

#check Eq >>>>> 2
#check (@Eq Nat) >>>>> 2

def shiftnat (n: Nat)(e : Expr) : MetaM Expr :=
  match n with
  | Nat.zero => return e
  | Nat.succ n => do
    let prev ← shiftnat n e
    return ← mkApp (mkConst `Nat.succ) prev  

syntax (name := natshift) term ">>+>>" term : term

@[termElab natshift] def natshiftImpl : TermElab :=
fun stx expectedType? =>
  match stx with
  | `($s >>+>> $t) =>
    do
      let e <- elabTerm s (some (Lean.mkConst `Nat))
      let n : Nat <- t.isNatLit?.getD 0
      return ←  shiftnat n e
  | _ => 
    do 
      return (Lean.mkConst `Nat) 

#check 3 >>+>> 2
#eval 3 >>+>> 12

#check Lean.Syntax.mkScientificLit (Float.toString 3.14)


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

def eglit := minletImpl (Syntax.mkStrLit "minlet!") none

#check eglit
#eval eglit

def blahh := Meta.isExprDefEqAux

def nameLess (name: Name) := 1

syntax (name := ignorename) "ignore!" ident : term

macro_rules
  | `(ignore! $s) => `(Nat.zero)

#check nameLess ``Nat.succ

#check ignore! Nat.succ

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
  
def makeIndFam : Nat → Type := by
  intro n
  induction n with
  | zero => 
    exact Nat
  | succ k ih =>
    exact Nat × ih

#check Eq.trans


def eqStatement: Prop := by
  apply Eq
  focus
    apply 1
  focus
    apply 2

def asFunc {α β : Type} (a: α) : (α → β) → β  := 
    fun f => f a

def asPi {α : Type}{motive : α → Type} (a: α) : 
      ((x : α) → motive x) → motive a :=
        fun f => f a    

def natGen : Nat := by
    apply (asFunc 3)
    exact Nat.succ

def piFactorizer (α : Type)(motive : α → Type) : Type :=
    (a: α ) → motive a

def island : Type := by
  apply piFactorizer
  focus
    exact fun _ => Nat
  focus
    exact Nat
  

def island2: Type := by
  apply piFactorizer Nat
  intro n
  induction n with
  | zero => exact Nat
  | succ k ih => exact Nat × ih

def egT := island2 

open Nat

def egEgt : island2 := fun n =>
  match n with
  | zero =>  Nat.zero
  | succ k  => (k, egEgt k)

def WithType := Σ A : Type, A

def WithType.mk (α : Type) (a : α) : WithType := ⟨α , a⟩

def WithType.getType (w : WithType) : Type := w.1
def WithType.getVal (w : WithType) : w.1 := w.2

def metaWithType(e: Expr) : MetaM Expr := do
  let tp <- inferType e
  let pair  ← mkAppM ``WithType.mk #[tp, e]
  return pair

syntax (name := withtype) "withType! " term : term

@[termElab withtype] def metaWithTypeStx : TermElab := 
  fun stx expectedType? =>
  match stx with
  | `(withType! $s) =>
    do 
      let e <- elabTerm s none
      let pair ← metaWithType e
      return pair
  | _ => Elab.throwIllFormedSyntax

def egName := ``Nat

#check egName

def egTyped  := withType! 3

#check egTyped
#check egTyped.getType

def elem : Nat := egTyped.getVal

#eval elem

def infEg : Inhabited Nat := inferInstance

#print infEg

#check @inferInstance (ToString Nat)

def viewExp : ToString Expr := inferInstance

def explicitToString (α : Type)(a: α)(ts: ToString α) : String :=
  ts.toString a

def exprToString (e: Expr) : String := viewExp.toString e

def exprView(e: Expr) : MetaM Expr := 
  do
    let tp ←  inferType e
    let tst ← mkAppM ``ToString #[tp]
    let ts ← synthInstance? tst
    match ts with
    | none => 
      do
        let viewExp : ToString Expr := inferInstance
        let litStr := Literal.strVal (viewExp.toString e)
        let strExp := mkLit litStr
        return  strExp
    | some t => do
      -- let tts ← mkAppM ``ToString.toString #[t] 
      let v ← -- mkAppN tts #[e]
         mkAppM ``explicitToString #[tp, e, t]
      return ← whnf v


syntax (name := showexpr) "show! " term : term

@[termElab showexpr] def showexprImpl : TermElab := 
  fun stx expectedType? =>
  match stx with
  | `(show! $s) =>
    do 
      let e <- elabTerm s none
      let s ← exprView e
      return s
  | _ => Elab.throwIllFormedSyntax

def egShow : String := show! (3 : Nat) 

#eval egShow

def egShow2 : String  := show! (fun n : Nat => 2 + n)

#eval egShow2

def hashExpr : Hashable Expr := inferInstance

#check hashExpr

theorem constfunc{α : Type}{f: Nat → α}:
        (∀ n: Nat, f n = f (succ n)) →  (∀ n: Nat, f n = f zero) := by
          intro hyp
          intro n 
          induction n with
          | zero => rfl
          | succ k ih =>
             rw [← ih]
             apply Eq.symm
             apply hyp

theorem constfuncGen{α : Type}{f: Nat → α}:
        (∀ n: Nat, f n = f (succ n)) →  
          (∃ c : α, ∀ n: Nat, f n = c) := by
          intro hyp
          apply Exists.intro
          intro n
          induction n with
          | zero => rfl
          | succ k ih =>
             rw [← ih]
             apply Eq.symm
             apply hyp 

def mvarMeta : MetaM Expr := do
  let mvar ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvarId := mvar.mvarId!
  let mvar2 ← mkFreshExprMVar (some (mkConst ``Nat)) -- none works too
  let mvarId2 := mvar2.mvarId!
  assignExprMVar mvarId2 mvar
  assignExprMVar mvarId (mkConst ``Nat.zero)
  let mvarUnused := mkFreshExprMVar (some (mkConst ``Nat))
  return mvar2

syntax (name := minass) "minass!" : term

@[termElab minass] def minAssImpl : TermElab :=
  fun stx expectedType? =>
    do
      let e ← mvarMeta
      return mkApp (mkConst ``Nat.succ) e

def chkMinAss  := minass!

#eval chkMinAss

variable {m n: Nat}

constant k : Nat

constant l: Nat

def kl := k * l

def cname := `k

#print kl

#print cname

def mn := m * n

def names := [`n, ``mn]

def nPlusOne := addone! n

#check nPlusOne
#print nPlusOne
#print mn

#eval @nPlusOne 3

#check ignore! n
#check ignore! pqrst

def useName (fn: Nat → Nat) (arg: Name) : MetaM Expr := 
  do
    let lctx ← getLCtx
    match (← getLCtx).findFromUserName? arg with
  | some d => return d.value
  | none   => return mkConst `Nat.zero 

def useFVar (z: Bool) (arg: Expr) : MetaM Expr := 
  do
    let lctx ← getLCtx
    let e ← lctx.getFVar! arg
    return mkApp (mkConst `Nat.succ) e.value

syntax (name := minname) "minname! " term : term

@[termElab minname] def minNameImpl : TermElab :=
  fun stx expectedType? =>
   match stx with
  | `(minname! $s) =>  
    do
      let n := Name.mkSimple "n"
      let z := Lean.mkConst `Nat.zero
      let ty := Lean.mkConst `Nat
      withLetDecl n ty z fun x =>
        let e := useFVar true x
        return ← e
  | _ => Elab.throwIllFormedSyntax

#eval minname! true
