import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Start with the fact that (a - b)^2 ≥ 0 for any real numbers
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  -- Expand (a - b)^2 using the identity (x - y)^2 = x^2 - 2xy + y^2
  have h_expanded : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := by
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      _ ≥ 0 := h
  -- Rearrange the inequality to get a^2 + b^2 ≥ 2*a*b
  linarith
