import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + (a - b) ≤ 1 := by
  have h₁ : a * b + (a - b) - 1 = (a - 1) * (b + 1) := by ring
  have h₂ : (a - 1) * (b + 1) ≤ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b + 1)]
  linarith
