import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- The square of any real number is nonnegative.
  have h_nonneg : (0 : ℝ) ≤ (a - b) ^ 2 := by
    exact pow_two_nonneg (a - b)
  -- Expand the square: `(a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b`.
  have h_expand : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
    ring
  -- Rewrite the nonnegativity using the expansion.
  have h_rewritten : (0 : ℝ) ≤ a ^ 2 + b ^ 2 - 2 * a * b := by
    simpa [h_expand] using h_nonneg
  -- The desired inequality follows by moving the term `2 * a * b` to the other side.
  linarith
