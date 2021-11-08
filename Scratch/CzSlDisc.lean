import Scratch.IntrosRwFind
universe u

variable {M: Type u}[Mul M]

set_option maxHeartbeats 1000000

theorem main_step : (∀ a b : M, (a * b) * b = a) →  (∀ a b : M, a * (a * b) = b) →  (m n: M)  → 
            (m * n) * m = n := by
    intros ax1 ax2 m n
    polyFind #⟨ax1, ax2, m, n⟩ 2 %⟨ax1, ax2, m, n, m * n⟩ save:mnn
    eqDeduc #⟨ax1, ax2, m, n⟩ 2 eqs:mnn save:mnn2 
    skip
    have lem4 : (m * n) * ((m * n) * n) = (m * n) * m := by
        lookup #⟨ax1, ax2, m, n⟩ mnn2
    skip
    have lem2 : (m * n) * ((m * n) * n) = n := by
        lookup #⟨ax1, ax2, m, n⟩ mnn
    skip
    exact sorry