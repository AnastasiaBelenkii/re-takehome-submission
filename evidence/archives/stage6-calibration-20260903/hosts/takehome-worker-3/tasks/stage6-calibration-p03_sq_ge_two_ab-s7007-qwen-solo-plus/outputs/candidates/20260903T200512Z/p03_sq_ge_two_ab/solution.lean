import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Since (a - b)^2 ≥ 0 for all real numbers
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  -- Expanding: a^2 - 2*a*b + b^2 ≥ 0
  -- Adding 2*a*b to both sides: a^2 + b^2 ≥ 2*a*b
  linarith [h]
