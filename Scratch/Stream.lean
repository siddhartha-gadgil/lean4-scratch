import Lean.Meta
open Nat
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

-- streams in the scala sense to memoize

inductive StreamSeq (α  : Type) : Type where
  | nil : StreamSeq α
  | cons : α → Thunk (StreamSeq α) → StreamSeq α
  deriving Inhabited

namespace StreamSeq

def get? (s : StreamSeq α) (n: Nat) : Option α  :=
  match s with
  | nil => none
  | cons x t => 
    match n with 
    | zero => some x
    | succ n' => get? (t.get) n'

partial def frm (n: Nat) : StreamSeq Nat := 
  cons n (Thunk.mk fun _ => (frm (succ n)))

partial def dyn {α : Type} (init : α) (iter : α → α) : StreamSeq α :=
  cons init (Thunk.mk fun _ => (dyn (iter init) iter))

partial def map {α β : Type} (f : α → β) (s : StreamSeq α) : StreamSeq β :=
  match s with
  | nil => nil
  | cons x t => cons (f x) (Thunk.mk fun _ => (map f t.get))

def takeList{α : Type}(n: Nat) (s : StreamSeq α) : List α :=
  match n with
  | zero => []
  | succ n' => match s with
    | nil => []
    | cons x t => x :: takeList n' t.get

end StreamSeq

def natSeq := (StreamSeq.frm 0) 

def threeOpt := natSeq.get? 3

#eval threeOpt

def doubler := StreamSeq.dyn 1 (fun x => x + x)

#eval doubler.get? 10

def fibPair : StreamSeq (Nat × Nat) :=
  StreamSeq.dyn (0, 1) (fun (x, y) => (y, x + y))

def fib := fibPair.map (fun (x, _) => x)

#eval fib.get? 40

def evolveShow {α : Type}[ToString α] (s: StreamSeq α) (n: Nat)  : TermElabM Unit :=
  match n with
  | zero => pure ()
  | succ n' => do
    let x := s.get? n'
    evolveShow s n' 
    Lean.Elab.logInfo m!"{n} : {x}"
    return ()


syntax (name:=logevolve) "evolve!" term "step" term: term

@[termElab logevolve] def logevolveImpl : TermElab :=
fun stx expectedType? =>
match stx with 
| `(evolve! $x step $y) =>
do
    let s ← elabTerm x none
    let n ← elabTerm y (mkConst `Nat)
    let expr ← mkAppM `evolveShow #[s, n]
    return expr
| _ => Elab.throwIllFormedSyntax

def ff := evolve! doubler step 5

#eval ff

def fff := evolve! doubler step 6

#eval fff

#eval doubler.takeList 25

inductive ListWit : List Nat → Prop where
  | data: (l : List Nat) → ListWit l

def factorThroughFn{α β : Type}(b : β ) : (β  → α ) → α   := 
    fun g => g b

def egn: Nat := by
  have l := List.range 20
  have lw := ListWit.data l
  have llw := ListWit.data (doubler.takeList 25)
  apply (factorThroughFn l)
  intro data
  exact 3
