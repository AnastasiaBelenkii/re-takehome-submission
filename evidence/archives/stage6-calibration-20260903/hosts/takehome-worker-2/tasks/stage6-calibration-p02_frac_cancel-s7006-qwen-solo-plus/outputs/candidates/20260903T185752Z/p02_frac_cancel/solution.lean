import Mathlib

/-- What is the value of `x` if `x = (2009 ^ 2 - 2009) / 2009`? Show that it is `2008`. -/
theorem p02_frac_cancel (x : ℝ) (h : x = (2009 ^ 2 - 2009) / 2009) : x = 2008 := by
  rw [h]
  -- Factor out 2009 from the numerator: 2009² - 2009 = 2009 * (2009 - 1)
  have h₁ : (2009 : ℝ) ^ 2 - 2009 = 2009 * (2009 - 1) := by
    ring
  rw [h₁]
  -- Cancel 2009 from numerator and denominator
  field_simp
  -- Compute 2009 - 1 = 2008
  norm_num
