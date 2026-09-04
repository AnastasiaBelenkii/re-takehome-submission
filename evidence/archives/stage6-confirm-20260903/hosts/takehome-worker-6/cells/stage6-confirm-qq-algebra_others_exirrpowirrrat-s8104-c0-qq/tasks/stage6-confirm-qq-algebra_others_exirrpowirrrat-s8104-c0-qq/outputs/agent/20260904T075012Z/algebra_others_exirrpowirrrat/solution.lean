import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  -- First establish that sqrt(2) is irrational
  have h_sqrt2_irrational : Irrational (Real.sqrt 2) := by
    apply Nat.Prime.irrational_sqrt
    decide
  
  -- Use the classical non-constructive argument
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 2: sqrt(2)^sqrt(2) is irrational
    -- Then let a = sqrt(2)^sqrt(2) and b = sqrt(2)
    -- a^b = (sqrt(2)^sqrt(2))^sqrt(2) = sqrt(2)^(sqrt(2)*sqrt(2)) = sqrt(2)^2 = 2, which is rational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, h, h_sqrt2_irrational, _⟩
    have h2 : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
      rw [← Real.rpow_mul]
      <;> ring_nf
      <;> norm_num
    rw [h2]
    intro h_irrational_2
    exact h_irrational_2 ⟨(2 : ℚ), by simp⟩
  · -- Case 1: sqrt(2)^sqrt(2) is rational
    -- Then let a = sqrt(2) and b = sqrt(2)
    -- a^b = sqrt(2)^sqrt(2), which is rational by assumption
    refine' ⟨Real.sqrt 2, Real.sqrt 2, h_sqrt2_irrational, h_sqrt2_irrational, _⟩
    exact h
