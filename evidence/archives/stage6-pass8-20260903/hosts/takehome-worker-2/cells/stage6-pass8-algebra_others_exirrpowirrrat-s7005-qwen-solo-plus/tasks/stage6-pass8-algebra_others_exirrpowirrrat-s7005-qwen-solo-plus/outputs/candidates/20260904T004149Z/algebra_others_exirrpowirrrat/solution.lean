import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  -- Use the classic non-constructive proof with sqrt(2)
  -- Consider whether sqrt(2)^sqrt(2) is rational or irrational
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · -- Case 1: sqrt(2)^sqrt(2) is irrational
    -- Take a = sqrt(2)^sqrt(2), b = sqrt(2)
    -- Then a^b = (sqrt(2)^sqrt(2))^sqrt(2) = sqrt(2)^2 = 2, which is rational
    refine' ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, h, irrational_sqrt_two, _⟩
    -- Show that (sqrt(2)^sqrt(2))^sqrt(2) = 2
    have h₁ : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
      rw [← Real.rpow_mul] <;> norm_num <;>
      linarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    -- Since 2 is rational, it's not irrational
    intro h₂
    apply h₂
    exact ⟨2 / 1, by simp [h₁]⟩
  · -- Case 2: sqrt(2)^sqrt(2) is rational
    -- Take a = sqrt(2), b = sqrt(2)
    -- Both are irrational, and a^b is rational by assumption
    refine' ⟨Real.sqrt 2, Real.sqrt 2, irrational_sqrt_two, irrational_sqrt_two, _⟩
    -- Since sqrt(2)^sqrt(2) is not irrational, it's rational
    intro h₂
    apply h
    exact h₂
