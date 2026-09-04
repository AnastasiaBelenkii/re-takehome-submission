import Mathlib

open Real

theorem algebra_others_exirrpowirrrat :
    ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a ^ b) := by
  classical
  let s : ℝ := Real.sqrt 2
  have hs_irr : Irrational s := by
    simpa using irrational_sqrt_two
  have hs_nonneg : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  by_cases hirr : Irrational (s ^ s)
  · -- a = s ^ s, b = s, then (a ^ b) = 2 is rational
    refine ⟨s ^ s, s, ?_, ?_, ?_⟩
    · exact hirr
    · exact hs_irr
    · intro hIrr
      have h_eq : (s ^ s) ^ s = (2 : ℝ) := by
        have h_mul : s * s = (2 : ℝ) := by
          simpa [s] using
            (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ)))
        calc
          (s ^ s) ^ s = s ^ (s * s) := (Real.rpow_mul hs_nonneg _ _).symm
          _ = s ^ (2 : ℝ) := by simpa [h_mul]
          _ = s ^ (2 : ℕ) := by
            simpa using (Real.rpow_natCast s 2)
          _ = s * s := by simpa [pow_two]
          _ = (2 : ℝ) := by
            simpa [s] using
              (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ)))
      have hIrr2 : Irrational (2 : ℝ) := by
        simpa [h_eq] using hIrr
      exact hIrr2 ⟨2, rfl⟩
  · -- s ^ s is rational, take a = s, b = s
    refine ⟨s, s, hs_irr, hs_irr, ?_⟩
    exact hirr
