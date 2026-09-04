import Mathlib

open Real

set_option maxHeartbeats 0

theorem algebra_others_exirrpowirrrat :
    ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a ^ b) := by
  classical
  have hs_irr : Irrational (Real.sqrt 2) := by
    simpa using irrational_sqrt_two
  have hpos : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  by_cases hirr : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- case: √2 ^ √2 is irrational
    refine ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, ?_, hs_irr, ?_⟩
    · exact hirr
    · intro hIrr
      have h_eq : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (2 : ℝ) := by
        calc
          ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2)
              = (Real.sqrt 2) ^ (Real.sqrt 2 * Real.sqrt 2) := by
                simpa using (Real.rpow_mul hpos (Real.sqrt 2) (Real.sqrt 2)).symm
          _ = (Real.sqrt 2) ^ (2 : ℝ) := by
                have : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
                  simpa using Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
                simpa [this]
          _ = (2 : ℝ) := by
                simp [Real.rpow_natCast, pow_two,
                      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      have h2 : Irrational (2 : ℝ) := by
        simpa [h_eq] using hIrr
      exact h2 ⟨2, rfl⟩
  · -- case: √2 ^ √2 is rational
    refine ⟨Real.sqrt 2, Real.sqrt 2, hs_irr, hs_irr, ?_⟩
    exact hirr
