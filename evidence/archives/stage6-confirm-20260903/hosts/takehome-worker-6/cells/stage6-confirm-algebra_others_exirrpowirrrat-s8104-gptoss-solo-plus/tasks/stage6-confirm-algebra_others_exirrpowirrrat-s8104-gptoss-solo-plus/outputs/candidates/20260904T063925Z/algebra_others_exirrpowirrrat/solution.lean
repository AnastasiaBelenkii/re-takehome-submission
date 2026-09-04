import Mathlib

open Real

theorem algebra_others_exirrpowirrrat :
    ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a ^ b) := by
  classical
  -- irrationality of √2
  have h_irr_sqrt2 : Irrational (Real.sqrt 2) := by
    simpa using irrational_sqrt_two
  -- consider whether √2 ^ √2 is rational
  by_cases h : ∃ q : ℚ, (q : ℝ) = (Real.sqrt 2) ^ (Real.sqrt 2)
  · -- rational case: take a = b = √2
    rcases h with ⟨q, hq⟩
    refine ⟨Real.sqrt 2, Real.sqrt 2, h_irr_sqrt2, h_irr_sqrt2, ?_⟩
    intro hIrr
    exact hIrr ⟨q, hq⟩
  · -- irrational case: set a = √2 ^ √2, b = √2, then a ^ b = 2 ∈ ℚ
    have h_irr_pow : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2)) := h
    have hx : (0 : ℝ) ≤ Real.sqrt 2 := by
      have : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      exact Real.sqrt_nonneg _
    have h_eq : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (2 : ℝ) := by
      calc
        ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2)
            = (Real.sqrt 2) ^ ((Real.sqrt 2) * (Real.sqrt 2)) := by
              have := Real.rpow_mul hx (Real.sqrt 2) (Real.sqrt 2)
              simpa using this.symm
        _ = (Real.sqrt 2) ^ (2 : ℝ) := by
              simpa [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        _ = (Real.sqrt 2) * (Real.sqrt 2) := by
              simpa using (Real.rpow_two (Real.sqrt 2))
        _ = (2 : ℝ) := by
              simpa [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    refine ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2,
            h_irr_pow, h_irr_sqrt2, ?_⟩
    intro hIrr
    have : ∃ q : ℚ, (q : ℝ) = ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) := by
      refine ⟨2, ?_⟩
      simpa using h_eq.symm
    exact hIrr this
