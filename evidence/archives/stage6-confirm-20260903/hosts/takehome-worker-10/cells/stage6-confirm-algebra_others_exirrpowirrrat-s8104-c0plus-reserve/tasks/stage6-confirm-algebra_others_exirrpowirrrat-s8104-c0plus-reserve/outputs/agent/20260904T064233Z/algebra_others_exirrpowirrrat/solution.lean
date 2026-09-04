import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  have h_sqrt2_irrational : Irrational (Real.sqrt 2) := by
    apply Nat.Prime.irrational_sqrt
    decide
  
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 1: (√2)^(√2) is irrational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, _, _, _⟩
    · -- Prove a is irrational
      exact h
    · -- Prove b is irrational
      exact h_sqrt2_irrational
    · -- Prove a^b is not irrational
      have h_nonneg : 0 ≤ Real.sqrt 2 := by positivity
      have h_pow : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
        calc
          ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2)
            = (Real.sqrt 2) ^ (Real.sqrt 2 * Real.sqrt 2) := by
              rw [← Real.rpow_mul h_nonneg]
          _ = (Real.sqrt 2) ^ (2 : ℝ) := by
            have h_sq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
              rw [Real.mul_self_sqrt (by positivity)]
            rw [h_sq]
          _ = 2 := by
            rw [Real.rpow_two]
            rw [Real.sq_sqrt (by positivity)]
      rw [h_pow]
      intro h_rat
      exact h_rat ⟨(2 : ℚ), by norm_num⟩
  · -- Case 2: (√2)^(√2) is rational
    refine' ⟨Real.sqrt 2, Real.sqrt 2, _, _, _⟩
    · -- Prove a is irrational
      exact h_sqrt2_irrational
    · -- Prove b is irrational
      exact h_sqrt2_irrational
    · -- Prove a^b is not irrational
      exact h
