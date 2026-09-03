import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  -- Expand: a * (2 - a) = 2*a - a^2
  -- We want to show 2*a - a^2 ≤ 1
  -- Rearranging: a^2 - 2*a + 1 ≥ 0
  -- This is (a - 1)^2 ≥ 0, which is always true
  have h : (a - 1)^2 ≥ 0 := sq_nonneg (a - 1)
  -- Use nlinarith to complete the algebraic manipulation
  nlinarith [h]
