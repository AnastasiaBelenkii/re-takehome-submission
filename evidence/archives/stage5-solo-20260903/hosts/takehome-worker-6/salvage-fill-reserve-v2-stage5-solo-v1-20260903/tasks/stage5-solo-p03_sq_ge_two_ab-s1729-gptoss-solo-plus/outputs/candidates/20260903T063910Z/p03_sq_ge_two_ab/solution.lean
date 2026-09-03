import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  have h : (a - b) ^ 2 ≥ 0 := by
    have : (a - b) * (a - b) ≥ 0 := mul_self_nonneg (a - b)
    simpa [pow_two] using this
  nlinarith
