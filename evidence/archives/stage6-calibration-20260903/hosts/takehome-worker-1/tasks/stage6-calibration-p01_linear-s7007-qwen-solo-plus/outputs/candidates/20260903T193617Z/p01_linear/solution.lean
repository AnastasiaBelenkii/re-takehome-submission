import Mathlib

/-- If `3 * x + 7 = 22` for a real number `x`, then `x = 5`. -/
theorem p01_linear (x : ℝ) (h : 3 * x + 7 = 22) : x = 5 := by
  -- Subtract 7 from both sides: 3 * x = 15
  have h1 : 3 * x = 15 := by
    rw [← sub_eq_zero] at h
    ring_nf at h ⊢
    linarith
  
  -- Divide by 3: x = 5
  have h2 : x = 5 := by
    apply mul_left_cancel₀ (show (3 : ℝ) ≠ 0 by norm_num)
    linarith
  
  exact h2
