import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  -- Use the classic sqrt(2) argument: either sqrt(2)^sqrt(2) is rational or it isn't
  have h_sqrt2_irrational : Irrational (Real.sqrt 2) := by
    apply Nat.Prime.irrational_sqrt
    decide
  
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 1: sqrt(2)^sqrt(2) is irrational
    -- Then let a = sqrt(2)^sqrt(2) and b = sqrt(2), so a^b = 2 which is rational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, h, h_sqrt2_irrational, _⟩
    intro h_rat
    have h_pow : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
      rw [← Real.rpow_mul (by positivity)]
      ring_nf
      <;> norm_num
    rw [h_pow] at h_rat
    exact h_rat ⟨2, by norm_num⟩
  · -- Case 2: sqrt(2)^sqrt(2) is rational
    -- Then let a = sqrt(2) and b = sqrt(2), both irrational, but a^b is rational
    refine' ⟨Real.sqrt 2, Real.sqrt 2, h_sqrt2_irrational, h_sqrt2_irrational, _⟩
    intro h_rat
    exact h h_rat
