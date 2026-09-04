import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  -- Use the classic proof with √2
  have h_sqrt2_irrat : Irrational (Real.sqrt 2) := by
    apply Nat.Prime.irrational_sqrt
    decide
  
  -- Consider whether (sqrt 2)^(sqrt 2) is rational or irrational
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 1: (sqrt 2)^(sqrt 2) is irrational
    -- Take a = (sqrt 2)^(sqrt 2), b = sqrt 2
    -- Both are irrational, and a^b = 2 which is rational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, h, h_sqrt2_irrat, _⟩
    have : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
      rw [← Real.rpow_mul] <;> norm_num <;> linarith [Real.sqrt_nonneg 2]
    rw [this]
    intro h_rat
    have : ¬ Irrational (2 : ℝ) := by
      intro h2
      exact h2 ⟨2, by simp⟩
    exact this h_rat
  · -- Case 2: (sqrt 2)^(sqrt 2) is rational
    -- Take a = sqrt 2, b = sqrt 2
    -- Both are irrational, and a^b = (sqrt 2)^(sqrt 2) is rational
    refine' ⟨Real.sqrt 2, Real.sqrt 2, h_sqrt2_irrat, h_sqrt2_irrat, _⟩
    intro h_rat
    exact h h_rat
