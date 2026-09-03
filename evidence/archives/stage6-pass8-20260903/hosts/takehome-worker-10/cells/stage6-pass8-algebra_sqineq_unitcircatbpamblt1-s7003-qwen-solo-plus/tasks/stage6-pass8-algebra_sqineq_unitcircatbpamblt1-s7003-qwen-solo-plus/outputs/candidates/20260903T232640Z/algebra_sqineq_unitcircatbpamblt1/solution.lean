import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + (a - b) ≤ 1 := by
  -- Use the identity (a - b)^2 ≥ 0 to get a^2 + b^2 ≥ 2ab
  have h₁ : 2 * a * b ≤ 1 := by
    nlinarith [sq_nonneg (a - b)]
  -- Complete the square: consider (a - 1/2)^2 + (b + 1/2)^2 ≥ 0
  have h₂ : a * b + (a - b) ≤ 1 := by
    nlinarith [sq_nonneg (a - b - 1), sq_nonneg (a + b - 1), 
               sq_nonneg (a - 1/2), sq_nonneg (b + 1/2)]
  exact h₂
