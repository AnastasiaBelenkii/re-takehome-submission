import Mathlib

/-- If `3 * x + 7 = 22` for a real number `x`, then `x = 5`. -/
theorem p01_linear (x : ℝ) (h : 3 * x + 7 = 22) : x = 5 := by
  -- The hypothesis is a linear equation in `x`.  `linarith` can solve such goals
  -- by converting the equality into a linear inequality system and eliminating
  -- variables.  Applying it directly resolves the goal.
  linarith
