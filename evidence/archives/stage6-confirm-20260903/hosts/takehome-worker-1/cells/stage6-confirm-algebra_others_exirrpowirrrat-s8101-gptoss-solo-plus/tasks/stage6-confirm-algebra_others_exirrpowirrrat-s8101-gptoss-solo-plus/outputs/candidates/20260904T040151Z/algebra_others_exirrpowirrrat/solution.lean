import Mathlib

open Real

theorem algebra_others_exirrpowirrrat :
    ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a ^ b) := by
  -- √2 is irrational.
  have h_irr_sqrt2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  -- Consider whether √2 ^ √2 is irrational.
  by_cases h : Irrational (Real.sqrt 2 ^ Real.sqrt 2)
  · -- In this case we take a = √2 ^ √2, b = √2.
    refine ⟨Real.sqrt 2 ^ Real.sqrt 2, Real.sqrt 2, ?_, ?_, ?_⟩
    · exact h
    · exact h_irr_sqrt2
    -- Show that (a ^ b) = 2, a rational number.
    intro hirr
    have hpow : (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 = (2 : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      calc
        (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2
            = Real.sqrt 2 ^ (Real.sqrt 2 * Real.sqrt 2) := by
              simpa [Real.rpow_mul hnonneg] using
                (Real.rpow_mul hnonneg (Real.sqrt 2) (Real.sqrt 2)).symm
        _ = Real.sqrt 2 ^ (2 : ℝ) := by
              have : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
                have : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
                simpa [Real.mul_self_sqrt this]
              simpa [this]
        _ = (Real.sqrt 2) ^ 2 := by
              simpa using (Real.rpow_natCast (Real.sqrt 2) 2)
        _ = (2 : ℝ) := by
              simpa [pow_two,
                Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    apply hirr
    exact ⟨2, hpow.symm⟩
  · -- Otherwise √2 ^ √2 is rational, and we can take a = b = √2.
    refine ⟨Real.sqrt 2, Real.sqrt 2, h_irr_sqrt2, h_irr_sqrt2, ?_⟩
    exact h
