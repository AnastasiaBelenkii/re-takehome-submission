import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  have h : (a - 1)^2 ≥ 0 := sq_nonneg (a - 1)
  -- (a - 1)^2 = a^2 - 2*a + 1 ≥ 0
  -- Expanding and rearranging: a^2 - 2*a + 1 ≥ 0
  -- This gives us: 2*a - a^2 ≤ 1
  -- Which is equivalent to a * (2 - a) ≤ 1
  nlinarith
