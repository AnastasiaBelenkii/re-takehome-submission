import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Start from the obvious nonnegativity of a square: (a - b)² ≥ 0.
  have h_nonneg : 0 ≤ (a - b) ^ 2 := by
    exact sq_nonneg (a - b)
  -- Expand the square to rewrite it in terms of `a` and `b`.
  have h_eq : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
    ring
  -- Using the equality, we obtain a nonnegativity statement for `a² + b² - 2ab`.
  have h' : 0 ≤ a ^ 2 + b ^ 2 - 2 * a * b := by
    simpa [h_eq] using h_nonneg
  -- Rearranging the inequality yields the desired result.
  linarith
