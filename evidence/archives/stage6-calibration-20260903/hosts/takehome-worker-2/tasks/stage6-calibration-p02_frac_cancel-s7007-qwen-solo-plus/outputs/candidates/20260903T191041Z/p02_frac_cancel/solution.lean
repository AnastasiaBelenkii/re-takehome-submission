import Mathlib

/-- What is the value of `x` if `x = (2009 ^ 2 - 2009) / 2009`? Show that it is `2008`. -/
theorem p02_frac_cancel (x : ℝ) (h : x = (2009 ^ 2 - 2009) / 2009) : x = 2008 := by
  rw [h]
  -- Rewrite x using the given equation
  -- Now we need to simplify (2009^2 - 2009) / 2009
  -- Factor: 2009^2 - 2009 = 2009 * (2009 - 1) = 2009 * 2008
  -- So (2009 * 2008) / 2009 = 2008
  norm_num
