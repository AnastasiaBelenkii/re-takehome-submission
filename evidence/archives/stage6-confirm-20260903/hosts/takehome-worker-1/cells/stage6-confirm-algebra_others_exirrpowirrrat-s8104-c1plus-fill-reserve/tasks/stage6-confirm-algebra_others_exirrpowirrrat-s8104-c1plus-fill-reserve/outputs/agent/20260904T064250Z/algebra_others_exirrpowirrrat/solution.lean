import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_others_exirrpowirrrat :
    ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a ^ b) := by
  -- Irrationality of √2.
  have h_irr_sqrt2 : Irrational (Real.sqrt 2) := by
    simpa using irrational_sqrt_two
  -- Classical case analysis on the irrationality of √2 ^ √2.
  by_cases h : Irrational (Real.sqrt 2 ^ Real.sqrt 2)
  · -- In this case √2 ^ √2 is irrational.
    refine ⟨Real.sqrt 2 ^ Real.sqrt 2, Real.sqrt 2, ?_, ?_, ?_⟩
    · exact h
    · exact h_irr_sqrt2
    · intro hIrr
      -- Compute (√2 ^ √2) ^ √2 = 2.
      have hpow : (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 = (2 : ℝ) := by
        have hx : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
        calc
          (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2
              = Real.sqrt 2 ^ (Real.sqrt 2 * Real.sqrt 2) := by
                rw [← Real.rpow_mul hx]
          _ = Real.sqrt 2 ^ (2 : ℝ) := by
                have : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
                  simpa using Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
                simpa [this]
          _ = Real.sqrt 2 * Real.sqrt 2 := by
                simpa using Real.rpow_two (Real.sqrt 2)
          _ = (2 : ℝ) := by
                simpa using Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
      -- Provide a rational witness for the value, contradicting irrationality.
      have : ∃ q : ℚ, (q : ℝ) = (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 :=
        ⟨2, by simpa [hpow]⟩
      exact hIrr this
  · -- Otherwise √2 ^ √2 is rational.
    refine ⟨Real.sqrt 2, Real.sqrt 2, ?_, ?_, ?_⟩
    · exact h_irr_sqrt2
    · exact h_irr_sqrt2
    · simpa using h
