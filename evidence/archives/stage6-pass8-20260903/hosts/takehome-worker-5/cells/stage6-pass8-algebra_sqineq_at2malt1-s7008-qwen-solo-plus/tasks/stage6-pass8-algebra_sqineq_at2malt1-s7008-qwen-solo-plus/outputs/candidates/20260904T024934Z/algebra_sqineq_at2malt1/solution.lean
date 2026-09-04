import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  -- Start with the fact that (a - 1)^2 ≥ 0 for any real a
  have h : (a - 1)^2 ≥ 0 := by nlinarith
  -- Expand (a - 1)^2 = a^2 - 2*a + 1 and rearrange
  have h2 : 2*a - a^2 ≤ 1 := by
    nlinarith [sq_nonneg (a - 1)]
  -- Note that a * (2 - a) = 2*a - a^2 by distributivity
  have h3 : a * (2 - a) = 2*a - a^2 := by ring
  -- Substitute and conclude
  rw [h3]
  exact h2
