import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  by_cases h₁ : a ≥ b
  · -- Case: a ≥ b, so |a - b| = a - b
    have h₂ : |a - b| = a - b := by
      rw [abs_of_nonneg (sub_nonneg.mpr h₁)]
    rw [h₂]
    -- Need to show ab + a - b ≤ 1
    nlinarith [sq_nonneg (a - b - 1)]
  · -- Case: a < b, so |a - b| = b - a
    have h₂ : a < b := lt_of_not_ge h₁
    have h₃ : |a - b| = b - a := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr h₂)]
    rw [h₃]
    -- Need to show ab + b - a ≤ 1
    nlinarith [sq_nonneg (b - a - 1)]
