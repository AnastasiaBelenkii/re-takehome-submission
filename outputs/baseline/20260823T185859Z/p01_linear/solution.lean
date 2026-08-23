import Mathlib

/-- If `3 * x + 7 = 22` for a real number `x`, then `x = 5`. -/
theorem p01_linear (x : ℝ) (h : 3 * x + 7 = 22) : x = 5 := by
  have h₁ : 3 * x = 15 := by linarith
  have h₂ : x = 5 := by
    apply mul_left_cancel₀ (show (3 : ℝ) ≠ 0 by norm_num)
    linarith
  exact h₂
