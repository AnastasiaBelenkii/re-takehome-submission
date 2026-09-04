import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  classical
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 1: sqrt(2)^(sqrt(2)) is irrational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, h, _, _⟩
    · -- Prove sqrt(2) is irrational
      exact irrational_sqrt_two
    · -- Prove (sqrt(2)^(sqrt(2)))^(sqrt(2)) is rational
      have h1 : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
        rw [← Real.rpow_mul]
        <;> norm_num
        <;> linarith [Real.sqrt_nonneg 2]
      rw [h1]
      -- Goal: ¬ Irrational 2
      -- Which is equivalent to ∃ q : ℚ, (q : ℝ) = 2
      exact fun h_irrat => h_irrat ⟨2, by norm_num⟩
  · -- Case 2: sqrt(2)^(sqrt(2)) is rational
    refine' ⟨Real.sqrt 2, Real.sqrt 2, _, _, _⟩
    · -- Prove sqrt(2) is irrational
      exact irrational_sqrt_two
    · -- Prove sqrt(2) is irrational
      exact irrational_sqrt_two
    · -- Prove sqrt(2)^(sqrt(2)) is rational (negation of irrational)
      exact h
