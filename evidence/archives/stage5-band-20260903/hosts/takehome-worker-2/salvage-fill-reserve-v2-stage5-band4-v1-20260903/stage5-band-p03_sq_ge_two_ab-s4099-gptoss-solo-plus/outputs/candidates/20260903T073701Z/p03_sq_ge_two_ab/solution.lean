import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Start from the nonnegativity of a square: (a - b)² ≥ 0.
  have h_nonneg : (0 : ℝ) ≤ (a - b) ^ 2 := by
    exact pow_two_nonneg (a - b)
  -- Rewrite (a - b)² using `sub_sq` to obtain an inequality involving `a²`, `b²` and `2ab`.
  have h_rewritten : (0 : ℝ) ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    simpa [sub_sq, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h_nonneg
  -- Rearrange the inequality to the desired form.
  linarith
