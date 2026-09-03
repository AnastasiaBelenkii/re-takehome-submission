import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  by_cases h₁ : a ≥ b
  · have h₂ : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr h₁)
    rw [h₂]
    nlinarith [sq_nonneg (a - b - 1)]
  · have h₂ : a < b := lt_of_not_ge h₁
    have h₃ : a - b ≤ 0 := sub_nonpos.mpr (le_of_lt h₂)
    have h₄ : |a - b| = b - a := by rw [abs_of_nonpos h₃]; ring
    rw [h₄]
    nlinarith [sq_nonneg (a - b + 1)]
