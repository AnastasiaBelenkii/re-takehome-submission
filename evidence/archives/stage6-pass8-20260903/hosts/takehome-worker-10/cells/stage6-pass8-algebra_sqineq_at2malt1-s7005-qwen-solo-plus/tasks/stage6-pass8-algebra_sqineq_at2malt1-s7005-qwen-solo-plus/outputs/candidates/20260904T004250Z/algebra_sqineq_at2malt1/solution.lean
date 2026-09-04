import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  -- We want to show a * (2 - a) ≤ 1
  -- Expanding: 2a - a² ≤ 1
  -- Rearranging: 0 ≤ 1 - 2a + a² = (a - 1)²
  -- Since squares are non-negative, (a - 1)² ≥ 0
  have h : (a - 1)^2 ≥ 0 := sq_nonneg (a - 1)
  -- From (a - 1)² ≥ 0, we get a² - 2a + 1 ≥ 0
  -- So a² - 2a ≥ -1, which means 2a - a² ≤ 1
  -- And 2a - a² = a * (2 - a)
  nlinarith
