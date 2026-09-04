import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  -- Classic proof: consider √2^√2
  -- Case 1: √2^√2 is rational, then a = √2, b = √2 works
  -- Case 2: √2^√2 is irrational, then a = √2^√2, b = √2 works since (√2^√2)^√2 = 2
  
  have h_sqrt2_irrat : Irrational (Real.sqrt 2) := by
    apply Nat.Prime.irrational_sqrt
    decide
  
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 2: √2^√2 is irrational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, _, _, _⟩
    · -- First component is irrational (assumption)
      exact h
    · -- Second component is irrational
      exact h_sqrt2_irrat
    · -- The power is rational: (√2^√2)^√2 = √2^(√2*√2) = √2^2 = 2
      have h1 : ¬ Irrational (((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2)) := by
        have h2 : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
          rw [← Real.rpow_mul]
          <;> norm_num
          <;> linarith [Real.sqrt_nonneg 2]
        rw [h2]
        intro h_rat
        exact h_rat ⟨2, by norm_num⟩
      exact h1
  · -- Case 1: √2^√2 is rational
    refine' ⟨Real.sqrt 2, Real.sqrt 2, _, _, _⟩
    · -- First component is irrational
      exact h_sqrt2_irrat
    · -- Second component is irrational
      exact h_sqrt2_irrat
    · -- The power is rational (by assumption)
      intro h_rat
      exact h h_rat
