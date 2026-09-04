import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  -- Note that (a - 1)^2 ≥ 0 for all real a since squares are non-negative
  have h : (a - 1)^2 ≥ 0 := sq_nonneg (a - 1)
  -- Expanding (a - 1)^2 gives a^2 - 2a + 1 ≥ 0
  -- Rearranging: 1 ≥ 2a - a^2 = a(2 - a)
  nlinarith [h]
