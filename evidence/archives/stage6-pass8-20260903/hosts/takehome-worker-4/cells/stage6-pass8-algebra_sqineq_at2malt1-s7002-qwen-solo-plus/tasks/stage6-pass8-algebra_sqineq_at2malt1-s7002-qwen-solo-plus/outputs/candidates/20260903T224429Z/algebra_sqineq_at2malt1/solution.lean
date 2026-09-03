import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  -- Use the fact that (a - 1)^2 ≥ 0 for any real a
  have h : (a - 1)^2 ≥ 0 := sq_nonneg (a - 1)
  have h₁ : a^2 - 2 * a + 1 ≥ 0 := by
    ring_nf at h ⊢
    exact h
  have h₂ : 1 ≥ 2 * a - a^2 := by
    linarith
  have h₃ : a * (2 - a) = 2 * a - a^2 := by
    ring
  rw [h₃]
  linarith
