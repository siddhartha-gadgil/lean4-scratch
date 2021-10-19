universe u

variable {M: Type u}[Mul M]

theorem CzSlOly : (∀ a b : M, (a * b) * b = a) → (∀ a b : M, a * (a * b) = b) →
            (m n: M) → m * n = n * m := by
              intros ax1 ax2 m n
              have lem1 : (m * n) * n = m := ax1 m n
              have lem2 : (m * n) * ((m * n) * n) = n := ax2 (m * n) n
              have lem4 : (m * n) * ((m * n) * n) = (m * n) * m := 
                  congrArg (fun x => (m * n) * x) lem1
              have lem5 : ((m * n) * m) * m = m * n:= ax1 (m * n) m
              have lem6 : (m * n) * m = n := by
                    rw [lem4] at lem2
                    assumption
              have lem7 : ((m * n) * m) * m = n * m  := 
                    congrArg (fun x => x * m) lem6 
              rw [lem5] at lem7
              assumption 
              