import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Apply the nonnegativity of the square `(a - b) ^ 2` and let `nlinarith` finish.
  nlinarith [sq_nonneg (a - b)]
