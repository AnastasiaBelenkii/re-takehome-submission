import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  -- Use the classic non-constructive proof with √2
  -- Consider whether √2^√2 is rational or irrational
  by_cases h : Irrational (Real.sqrt 2 ^ Real.sqrt 2)
  · -- Case 1: √2^√2 is irrational
    -- Take a = √2^√2 and b = √2
    -- Then a^b = (√2^√2)^√2 = √2^2 = 2, which is rational
    refine' ⟨Real.sqrt 2 ^ Real.sqrt 2, Real.sqrt 2, h, _, _⟩
    · -- Prove Irrational (Real.sqrt 2)
      exact irrational_sqrt_two
    · -- Prove ¬ Irrational ((Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2)
      have h1 : (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 = 2 := by
        rw [← Real.rpow_mul]
        <;> ring_nf
        <;> norm_num [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
      rw [h1]
      exact fun h2 => h2 ⟨2, by norm_num⟩
  · -- Case 2: √2^√2 is rational
    -- Take a = √2 and b = √2
    -- Both are irrational but a^b = √2^√2 is rational
    refine' ⟨Real.sqrt 2, Real.sqrt 2, _, _, h⟩
    · -- Prove Irrational (Real.sqrt 2)
      exact irrational_sqrt_two
    · -- Prove Irrational (Real.sqrt 2)
      exact irrational_sqrt_two
