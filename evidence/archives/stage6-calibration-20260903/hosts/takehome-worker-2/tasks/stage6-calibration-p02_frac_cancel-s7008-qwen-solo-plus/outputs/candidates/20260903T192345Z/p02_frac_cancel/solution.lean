import Mathlib

/-- What is the value of `x` if `x = (2009 ^ 2 - 2009) / 2009`? Show that it is `2008`. -/
theorem p02_frac_cancel (x : ℝ) (h : x = (2009 ^ 2 - 2009) / 2009) : x = 2008 := by
  rw [h]
  -- Rewrite x using the given hypothesis
  have h₁ : (2009 : ℝ) ^ 2 - 2009 = 2009 * (2009 - 1) := by
    ring
  -- Factor out 2009 from the numerator
  rw [h₁]
  -- Now we have (2009 * (2009 - 1)) / 2009
  field_simp
  -- Cancel 2009 in numerator and denominator
  norm_num
  -- Compute 2009 - 1 = 2008
