import Mathlib

/-- What is the value of `x` if `x = (2009 ^ 2 - 2009) / 2009`? Show that it is `2008`. -/
theorem p02_frac_cancel (x : ℝ) (h : x = (2009 ^ 2 - 2009) / 2009) : x = 2008 := by
  rw [h]
  -- Rewrite x using the given hypothesis
  have h₁ : (2009 : ℝ) ≠ 0 := by norm_num
  -- Verify 2009 is nonzero for valid division
  field_simp [h₁]
  -- Cancel 2009 in numerator and denominator
  norm_num
