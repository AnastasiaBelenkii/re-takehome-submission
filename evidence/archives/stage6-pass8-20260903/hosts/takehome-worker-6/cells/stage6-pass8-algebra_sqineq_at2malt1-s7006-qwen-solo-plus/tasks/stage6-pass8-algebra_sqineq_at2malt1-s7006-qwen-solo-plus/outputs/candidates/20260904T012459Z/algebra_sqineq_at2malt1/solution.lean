import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  -- Expand: a * (2 - a) = 2*a - a^2
  -- We want to show 2*a - a^2 ≤ 1
  -- This is equivalent to showing 0 ≤ 1 - 2*a + a^2
  -- Note that 1 - 2*a + a^2 = (a - 1)^2
  -- Since squares are non-negative, (a - 1)^2 ≥ 0
  have h : (a - 1)^2 ≥ 0 := sq_nonneg (a - 1)
  -- From (a - 1)^2 ≥ 0, we get a^2 - 2*a + 1 ≥ 0
  -- Rearranging: 2*a - a^2 ≤ 1
  -- And since a * (2 - a) = 2*a - a^2, we're done
  nlinarith [h]
