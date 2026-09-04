import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  have h_sqrt2_irrat : Irrational (Real.sqrt 2) := by
    apply Nat.Prime.irrational_sqrt
    decide
  
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 2: (√2)^(√2) is irrational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, h, h_sqrt2_irrat, _⟩
    have h2 : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
      have h_pos : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      calc
        ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (Real.sqrt 2) ^ (Real.sqrt 2 * Real.sqrt 2) := by
          rw [← Real.rpow_mul h_pos]
        _ = (Real.sqrt 2) ^ 2 := by
          rw [Real.mul_self_sqrt]
          <;> norm_num
        _ = 2 := by
          rw [Real.sq_sqrt (by norm_num)]
    rw [h2]
    intro h3
    exact h3 ⟨2, by norm_num⟩
  · -- Case 1: (√2)^(√2) is rational
    refine' ⟨Real.sqrt 2, Real.sqrt 2, h_sqrt2_irrat, h_sqrt2_irrat, _⟩
    intro h3
    exact h h3
