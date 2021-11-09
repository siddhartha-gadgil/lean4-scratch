import Scratch.IntrosRwFind
universe u

variable {M: Type u}[Mul M]

set_option maxHeartbeats 5000000

theorem main_step : (∀ a b : M, (a * b) * b = a) →  (∀ a b : M, a * (a * b) = b) →  (m n: M)  → 
            (m * n) * m = n := by
    intros ax1 ax2 m n
    polyFind #⟨ax1, ax2, m, n, m * n⟩ 2 save:mnn
    eqDeduc #⟨ax1, ax2, m, n⟩ 2 eqs:mnn save:mnn2 
    propeqs  mnn2
