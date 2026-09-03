import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Use the fact that any square is nonnegative.
  have h : 0 ≤ (a - b) ^ 2 := by
    exact sq_nonneg (a - b)
  -- Expand the square and simplify; the resulting inequality is exactly the goal.
  nlinarith [h]
