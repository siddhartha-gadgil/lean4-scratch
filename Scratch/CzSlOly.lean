import Scratch.IntrosRwFind
universe u

variable {M: Type u}[Mul M]

theorem CzSlOly : (∀ a b : M, (a * b) * b = a) → (∀ a b : M, a * (a * b) = b) →
            (m n: M) → m * n = n * m := by
              intros ax1 ax2 m n
              have lem1 : (m * n) * n = m := ax1 m n
              have lem2 : (m * n) * ((m * n) * n) = n := ax2 (m * n) n
              have lem3 : ((m * n) * m) * m = m * n  := ax1 (m * n) m
              have lem4 : (m * n) * ((m * n) * n) = (m * n) * m := 
                  congrArg (fun x => (m * n) * x) lem1              
              have lem5 : (m * n) * m = n := by
                    rw [lem4] at lem2
                    assumption
              have lem6 : ((m * n) * m) * m = n * m  := 
                    congrArg (fun x => x * m) lem5 
              rw [lem3] at lem6
              assumption 

example : (∀ a b : M, (a * b) * b = a) → (∀ a b : M, a * (a * b) = b) →
            (m n : M) →  (m * n) * n = m := by
            introsRwFind 2

set_option maxHeartbeats 200000


example : (∀ a b : M, (a * b) * b = a) → (m n: M)  → m * n * n = m := by
    introsRwFind 2

example : (∀ a b : M, (a * b) * b = a) → (m n: M)  → m * n * n = m := by
    intros eq m n
    polyFind #⟨eq, m, n⟩ 2

example : (∀ a b : M, (a * b) * b = a) → (m n: M)  → m * (m * n * n) = m * m := by
    intros eq m n
    polyFind #⟨eq, m, n⟩ 2 save:mnn
    eqDeduc #⟨eq, m, n⟩ 1 eqs:mnn

example : (∀ a b : M, (a * b) * b = a) → (m n: M)  → 
            (m * n * n) * (m * n) = m * (m * n) := by
    intros eq m n
    polyFind #⟨eq, m, n⟩ 2 save:mnn
    eqDeduc #⟨eq, m, n⟩ 2 eqs:mnn

example : (∀ a b : M, (a * b) * b = a) → (m n: M)  → 
            (m * n) * ((m * n) * n) = (m * n) * m := by
    intros eq m n
    polyFind #⟨eq, m, n, m *n⟩ 1 save:mmnn
    eqDeduc #⟨eq, m, n, m * n⟩ 1 eqs:mnn save:mmnn2
/-
example : (∀ a b : M, (a * b) * b = a) →  (∀ a b : M, a * (a * b) = b) →  (m n: M)  → 
            (m * n) * m = n := by
    intros eq1 eq2 m n
    polyFind #⟨eq1, eq2, m, n⟩ 2 save:mnn
    eqDeduc #⟨eq1, eq2, m, n⟩ 2 eqs:mnn save:mnn2 -- max heartbeat here
    polyFind #⟨eq1, eq2, m, n⟩ 1 load:mnn2
-/

#check fun (m: M) => HMul.hMul m 

#check @HMul.hMul

def mn := fun m : M => fun n: M => nameapply! HMul.hMul at m with n

#check @mn