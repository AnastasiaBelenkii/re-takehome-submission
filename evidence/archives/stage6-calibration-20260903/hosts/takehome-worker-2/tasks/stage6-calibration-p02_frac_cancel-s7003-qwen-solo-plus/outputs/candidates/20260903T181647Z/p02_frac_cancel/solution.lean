import Mathlib

/-- What is the value of `x` if `x = (2009 ^ 2 - 2009) / 2009`? Show that it is `2008`. -/
theorem p02_frac_cancel (x : ℝ) (h : x = (2009 ^ 2 - 2009) / 2009) : x = 2008 := by
  rw [h]
  -- Substitute the definition of x into the goal
  -- Now we need to show (2009 ^ 2 - 2009) / 2009 = 2008
  -- Factor out 2009: (2009 * 2009 - 2009 * 1) / 2009 = 2009 * (2009 - 1) / 2009 = 2009 - 1 = 2008
  norm_num
