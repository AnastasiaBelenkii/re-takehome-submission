import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Start with the fact that (a - b)^2 ≥ 0 since squares are non-negative
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  -- Expand (a - b)^2 = a^2 - 2*a*b + b^2 using ring expansion
  have h_expanded : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  -- Substitute the expansion into the inequality
  rw [h_expanded] at h
  -- Rearrange to get a^2 + b^2 ≥ 2*a*b by adding 2*a*b to both sides
  linarith
