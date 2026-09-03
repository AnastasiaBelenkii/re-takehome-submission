import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Proof sketch:
  -- 1. The square of any real number is nonnegative, so `(a - b) ^ 2 ≥ 0`.
  -- 2. Expanding `(a - b) ^ 2` yields `a ^ 2 - 2 * a * b + b ^ 2`.
  -- 3. Rearranging this inequality gives `a ^ 2 + b ^ 2 ≥ 2 * a * b`.
  -- We invoke `sq_nonneg` for the nonnegativity and let `nlinarith` finish.
  nlinarith [sq_nonneg (a - b)]
