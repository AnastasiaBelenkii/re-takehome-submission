import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + (a - b) ≤ 1 := by
  have h₁ : (a - b - 1)^2 ≥ 0 := sq_nonneg (a - b - 1)
  have h₂ : (a - b - 1)^2 = 2 - 2 * (a * b + a - b) := by
    calc
      (a - b - 1)^2 = a^2 + b^2 + 1 - 2 * a * b - 2 * a + 2 * b := by ring
      _ = 1 + 1 - 2 * a * b - 2 * a + 2 * b := by rw [h₀]
      _ = 2 - 2 * (a * b + a - b) := by ring
  have h₃ : 2 - 2 * (a * b + a - b) ≥ 0 := by linarith [h₁, h₂]
  linarith
