import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- The square of any real number is non-negative
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  -- Expand (a - b)^2 using ring expansion
  have h_expanded : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  -- Substitute the expanded form into the inequality
  have h_ineq : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := by rw [h_expanded] at h; exact h
  -- Rearrange terms to get the desired inequality
  linarith
