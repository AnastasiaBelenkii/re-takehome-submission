import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  -- Expand the left side: a * (2 - a) = 2*a - a^2
  -- We want to show 2*a - a^2 ≤ 1
  -- This is equivalent to showing 0 ≤ 1 - 2*a + a^2
  -- Which is 0 ≤ (a - 1)^2
  -- Since squares are always non-negative, this holds
  have h : (a - 1)^2 ≥ 0 := sq_nonneg (a - 1)
  -- Expand (a - 1)^2 = a^2 - 2*a + 1
  -- So a^2 - 2*a + 1 ≥ 0
  -- Therefore 1 ≥ 2*a - a^2
  -- And 2*a - a^2 = a * (2 - a)
  calc
    a * (2 - a) = 2 * a - a ^ 2 := by ring
    _ ≤ 1 := by
      -- From (a - 1)^2 ≥ 0, we get a^2 - 2*a + 1 ≥ 0
      -- So 1 ≥ 2*a - a^2
      linarith [sq_nonneg (a - 1)]
