namespace PolyMath

inductive Letter where
  | α : Letter
  | β : Letter 
  | α! : Letter
  | β! : Letter
  deriving DecidableEq, Repr

def Letter.inv : Letter → Letter
  | α => α!
  | β  => β!
  | α! => α 
  | β! => β 

postfix:100 "⁻¹" => Letter.inv

open Letter

abbrev Word := List Letter

def Word.pow : Word → Nat → Word :=
  fun w n => 
  match n with
  | 0 => []
  | Nat.succ m => w ++ (pow w m)

def Word.conj: Word → Letter → Word
  | w, l => [l] ++ w ++ [l⁻¹]

instance : Pow Word Nat where
  pow w n := w.pow n

instance: Pow Word Letter where
  pow w l := w.conj l

def splits(l : Letter) : Word → List (Word × Word) 
  | [] => []
  | x :: ys =>
    let tailSplits := (splits l ys).map (fun (fst, snd) => (x :: fst, snd)) 
    if x = l then ([], ys) :: tailSplits else tailSplits

#eval splits α [β, α, β, α, β⁻¹]

partial def l : Word → Nat  
  | [] => 0
  | x :: ys =>
    let base := 1 + (l ys)
    let derived := (splits (x⁻¹) ys).map (fun (fst, snd) => l fst + l snd) 
    derived.foldl min base

#eval l ([α, α, β, α!, β!])

#eval l ([α, α, β, α!, β!]^2)

structure ProvedSplit (l: Letter)(w : Word) where
  fst : Word
  snd: Word
  proof : w = fst ++ [l] ++ snd 

def ProvedSplit.head (x: Letter) (ys: Word) : ProvedSplit x (x :: ys) :=
  ⟨[], ys, rfl⟩

def ProvedSplit.prepend{l: Letter}{w : Word} (x: Letter) 
        (ps: ProvedSplit l w) : ProvedSplit l (x :: w) :=
      let newFst := x :: ps.fst
      let newSnd := ps.snd
      have newProof : x :: w = newFst ++ [l] ++ newSnd  := 
        by
          let prev : x :: w = x :: (ps.fst ++ [l] ++ ps.snd) 
             := congrArg  (List.cons x) ps.proof
          rw [prev] 
          simp
      ⟨newFst, newSnd, newProof⟩   


theorem conj_split (x: Letter) (ys fst snd: Word) :
          ys = fst ++ [x⁻¹] ++ snd → x :: ys = fst^x ++ snd :=
            by
              intro hyp
              have expand : fst^x = [x] ++ fst ++ [x⁻¹] := rfl
              rw [expand] 
              have lemma := 
                    congrArg (List.cons x) hyp
              rw [hyp]
              simp

abbrev Length := Word → Nat

def conjInv(l: Length) : Prop := 
    (x : Letter) → (g : Word) → l (g^x) = l (g)

def triangIneq(l: Length) : Prop := 
    (g h : Word) → l (g ++ h) ≤ l g + l h

def normalized(l: Length) : Prop :=
    (x : Letter) → l [x] = 1

structure ProvedBound(g: Word):  Type where
  bound: Nat 
  pf : (l: Length) → normalized l → conjInv l → triangIneq l → l g ≤ bound

def conjBound(x: Letter)(ys fst snd: Word)(eqn : ys = fst ++ [x⁻¹] ++ snd) :
        ProvedBound fst → ProvedBound snd → ProvedBound (x :: ys) := 
          fun pb1 pb2 =>
          let bound := pb1.bound + pb2.bound
          let pf : 
            (l: Length) → normalized l → conjInv l → triangIneq l → 
                l (x :: ys) ≤ bound := by
                  intros l norm conj triang
                  rw [conj_split x ys fst snd eqn]
                  have lem : l (fst ^ x ++ snd) ≤ l (fst^x) + l snd := 
                     by
                       apply triang
                  skip
                  have clem : l (fst^x) = l fst := by apply conj
                  rw [clem] at lem
                  apply Nat.le_trans lem
                  have l1 : l fst ≤ pb1.bound := pb1.pf l norm conj triang
                  have l2 : l snd ≤ pb2.bound := pb2.pf l norm conj triang
                  apply Nat.add_le_add l1 l2
          ⟨bound, pf⟩

def ProvedBound.prepend{w : Word} (x: Letter) 
        (ps: ProvedBound w) : ProvedBound (x :: w) :=
      let newBound := ps.bound + 1
      ⟨newBound, fun l norm conj triang => by
        let prev := ps.pf l norm conj triang
        have lemTri : l (x :: w) ≤ l ([x]) + l w := 
          by
            apply triang [x] 
        skip
        apply Nat.le_trans lemTri
        have gen : l [x] = 1 := norm x
        rw [gen]
        rw [Nat.add_comm]
        apply Nat.add_le_add_right prev  
        ⟩

def ProvedBound.min {w: Word}: ProvedBound w → List (ProvedBound w) → 
    ProvedBound w :=
        fun head tail =>
          tail.foldl (fun pb1 pb2 =>
            if pb1.bound ≤ pb2.bound then pb1 else pb2) head

def ProvedBound.empty: ProvedBound [] :=
  ⟨0, sorry⟩


def provedSplits(z: Letter) : (w : Word) → List (ProvedSplit z w) 
  | [] => []
  | x :: ys =>
    let tailSplits := (provedSplits z ys).map (
        fun ps => ps.prepend x) 
    if c:x = z then
      let headSplit : ProvedSplit z (x :: ys) :=
        by
          rw [c] 
          exact ProvedSplit.head z ys 
      headSplit :: tailSplits
    else tailSplits

#eval (provedSplits α [β, α, β, α, β⁻¹]).map (fun ps => (ps.fst, ps.snd))

#check Nat.add_le_add_right

end PolyMath