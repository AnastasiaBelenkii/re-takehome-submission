import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Use the fact that squares are non-negative: (a - b)^2 ≥ 0
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  -- Expand (a - b)^2 = a^2 - 2*a*b + b^2 and rearrange to get the result
  linarith [h]
