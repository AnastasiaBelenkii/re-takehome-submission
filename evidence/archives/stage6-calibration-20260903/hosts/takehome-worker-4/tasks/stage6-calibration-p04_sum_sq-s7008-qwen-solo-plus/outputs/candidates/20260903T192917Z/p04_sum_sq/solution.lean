import Mathlib

/-- Real numbers `x` and `y` satisfy `x + y = 13` and `x * y = 24`.
Show that `x ^ 2 + y ^ 2 = 121`. -/
theorem p04_sum_sq (x y : ℝ) (h1 : x + y = 13) (h2 : x * y = 24) : x ^ 2 + y ^ 2 = 121 := by
  -- Use the algebraic identity (x + y)^2 = x^2 + 2xy + y^2
  -- Rearranging gives x^2 + y^2 = (x + y)^2 - 2xy
  have h3 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    ring
  -- Substitute the given values for x + y and xy
  rw [h3, h1, h2]
  -- Compute the numerical result: 13^2 - 2*24 = 169 - 48 = 121
  norm_num
