import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- We know that (a - b)^2 ≥ 0 for any real numbers a and b
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  -- Expanding gives a^2 - 2*a*b + b^2 ≥ 0
  have h_expanded : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := by
    rw [sub_sq] at h
    exact h
  -- Adding 2*a*b to both sides gives a^2 + b^2 ≥ 2*a*b
  linarith
