import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  -- Use the classic proof: consider √2 and (√2)^(√2)
  -- Case 1: (√2)^(√2) is rational - then a = b = √2 works
  -- Case 2: (√2)^(√2) is irrational - then a = (√2)^(√2), b = √2 gives a^b = 2
  
  have h_sqrt2_irrat : Irrational (Real.sqrt 2) := by
    apply Nat.Prime.irrational_sqrt
    decide
  
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 2: (√2)^(√2) is irrational
    -- Let a = (√2)^(√2) and b = √2
    -- Then a^b = ((√2)^(√2))^√2 = (√2)^2 = 2, which is rational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, h, h_sqrt2_irrat, _⟩
    -- Need to show ¬ Irrational (a^b), i.e., a^b is rational
    have : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num
      <;> ring_nf
      <;> norm_num
    rw [this]
    exact fun h_rat => h_rat ⟨2, by norm_num⟩
  · -- Case 1: (√2)^(√2) is rational
    -- Let a = b = √2
    -- Then a^b = (√2)^(√2), which is rational by assumption
    refine' ⟨Real.sqrt 2, Real.sqrt 2, h_sqrt2_irrat, h_sqrt2_irrat, _⟩
    -- Need to show ¬ Irrational (a^b), i.e., a^b is rational
    exact h
