import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + (a - b) ≤ 1 := by
  -- Use the constraint a² + b² = 1 to rewrite 1 - (ab + a - b)
  -- Show that 1 - ab - a + b ≥ 0 by completing the square
  have h₁ : 1 - a * b - a + b ≥ 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (a - b), 
               sq_nonneg (a + b - 1), sq_nonneg (a + b + 1)]
  -- Rearrange to get the desired inequality
  linarith
