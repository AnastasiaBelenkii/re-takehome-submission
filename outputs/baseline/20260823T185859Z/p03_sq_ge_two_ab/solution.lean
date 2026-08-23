import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  have h2 : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  rw [h2] at h
  linarith
