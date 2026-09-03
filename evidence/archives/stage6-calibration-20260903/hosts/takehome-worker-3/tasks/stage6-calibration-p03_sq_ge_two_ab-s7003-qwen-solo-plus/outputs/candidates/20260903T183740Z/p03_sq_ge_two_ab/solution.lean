import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Proof sketch:
  -- 1. Start with (a - b)^2 ≥ 0 since squares of reals are non-negative
  -- 2. Expand (a - b)^2 = a^2 - 2*a*b + b^2
  -- 3. Rearrange to get a^2 + b^2 ≥ 2*a*b
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  calc
    a ^ 2 + b ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 + 2 * a * b := by ring
    _ = (a - b) ^ 2 + 2 * a * b := by ring
    _ ≥ 0 + 2 * a * b := by gcongr
    _ = 2 * a * b := by ring
