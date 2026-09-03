import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- We know that (a - b)^2 ≥ 0 for any real numbers a and b
  have h : (a - b) ^ 2 ≥ 0 := by nlinarith
  -- Expanding (a - b)^2 gives a^2 - 2*a*b + b^2 ≥ 0
  -- Adding 2*a*b to both sides gives a^2 + b^2 ≥ 2*a*b
  linarith [h]
