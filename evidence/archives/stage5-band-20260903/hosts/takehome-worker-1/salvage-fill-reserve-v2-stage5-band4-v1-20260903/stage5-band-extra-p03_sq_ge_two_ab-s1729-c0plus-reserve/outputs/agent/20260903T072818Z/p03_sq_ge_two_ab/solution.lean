import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Start with the fact that (a - b)^2 ≥ 0 for any real numbers
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg _
  -- Expand (a - b)^2 = a^2 - 2ab + b^2 using algebraic manipulation
  have h_exp : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  -- Substitute the expansion into the inequality
  rw [h_exp] at h
  -- Rearrange terms to get a^2 + b^2 ≥ 2ab
  linarith
