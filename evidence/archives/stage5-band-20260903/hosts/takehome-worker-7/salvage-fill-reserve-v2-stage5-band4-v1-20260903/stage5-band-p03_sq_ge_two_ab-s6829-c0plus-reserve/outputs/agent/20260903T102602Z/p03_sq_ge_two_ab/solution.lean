import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- We know that (a - b)^2 ≥ 0 for any real numbers a and b
  have h : (a - b) ^ 2 ≥ 0 := by
    exact sq_nonneg (a - b)
  -- Expanding (a - b)^2 gives a^2 - 2*a*b + b^2
  have h_expanded : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
    ring
  -- Substituting the expansion into the inequality
  have h_ineq : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := by
    rw [h_expanded] at h
    exact h
  -- Rearranging to get a^2 + b^2 ≥ 2*a*b
  linarith
