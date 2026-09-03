import Mathlib

/-- Real numbers `x` and `y` satisfy `x + y = 13` and `x * y = 24`.
Show that `x ^ 2 + y ^ 2 = 121`. -/
theorem p04_sum_sq (x y : ℝ) (h1 : x + y = 13) (h2 : x * y = 24) : x ^ 2 + y ^ 2 = 121 := by
  -- Use the algebraic identity (x + y)^2 = x^2 + 2xy + y^2
  have h3 : (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
  -- Substitute the given values into the identity
  rw [h1, h2] at h3
  -- Simplify: 13^2 = x^2 + 2*24 + y^2, so 169 = x^2 + 48 + y^2
  norm_num at h3 ⊢
  -- Rearrange to get x^2 + y^2 = 121
  linarith
