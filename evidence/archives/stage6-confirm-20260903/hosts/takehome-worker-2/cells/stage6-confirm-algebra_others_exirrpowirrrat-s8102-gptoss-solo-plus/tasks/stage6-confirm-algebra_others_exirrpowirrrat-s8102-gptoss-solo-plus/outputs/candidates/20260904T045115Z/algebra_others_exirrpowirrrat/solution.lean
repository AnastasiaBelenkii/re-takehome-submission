import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_others_exirrpowirrrat :
    ∃ a b : ℝ, Irrational a ∧ Irrational b ∧ ¬ Irrational (a ^ b) := by
  classical
  have h_irr_sqrt2 : Irrational (Real.sqrt 2) := by
    simpa using irrational_sqrt_two
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- `√2 ^ √2` is irrational; use it as `a`
    refine ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, ?_, ?_, ?_⟩
    · exact h
    · exact h_irr_sqrt2
    · intro hIrr
      have hx : (0 : ℝ) ≤ Real.sqrt 2 := by
        simpa using Real.sqrt_nonneg (2)
      have h_eq : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (2 : ℝ) := by
        calc
          ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2)
              = (Real.sqrt 2) ^ (Real.sqrt 2 * Real.sqrt 2) := by
                simpa using (Real.rpow_mul hx (Real.sqrt 2) (Real.sqrt 2)).symm
          _ = (Real.sqrt 2) ^ (2 : ℝ) := by
                have h_mul : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
                  simpa using Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
                simpa [h_mul]
          _ = (2 : ℝ) := by
                simpa [Real.rpow_natCast, pow_two,
                  Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      have hIrr2 : Irrational (2 : ℝ) := by
        simpa [h_eq] using hIrr
      exact hIrr2 ⟨2, by norm_cast⟩
  · -- `√2 ^ √2` is rational; take both numbers equal to `√2`
    refine ⟨Real.sqrt 2, Real.sqrt 2, ?_, ?_, ?_⟩
    · exact h_irr_sqrt2
    · exact h_irr_sqrt2
    · exact h
