import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  have h : (a - b) ^ 2 ≥ 0 := by
    -- Square of any real number is non-negative
    exact sq_nonneg (a - b)
  -- Expand (a - b)^2 = a^2 - 2*a*b + b^2
  calc
    a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * a * b := by ring
    _ ≥ 0 + 2 * a * b := by gcongr <;> assumption
    _ = 2 * a * b := by ring
