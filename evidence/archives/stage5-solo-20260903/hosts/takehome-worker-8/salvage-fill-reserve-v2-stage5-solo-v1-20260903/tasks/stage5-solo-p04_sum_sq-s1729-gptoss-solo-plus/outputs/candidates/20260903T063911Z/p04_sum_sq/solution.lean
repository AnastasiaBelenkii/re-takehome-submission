import Mathlib

/-- Real numbers `x` and `y` satisfy `x + y = 13` and `x * y = 24`.
Show that `x ^ 2 + y ^ 2 = 121`. -/
theorem p04_sum_sq (x y : ℝ) (h1 : x + y = 13) (h2 : x * y = 24) : x ^ 2 + y ^ 2 = 121 := by
  -- Use the algebraic identity `x^2 + y^2 = (x + y)^2 - 2 * (x * y)`.
  have h_identity : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    ring
  -- Substitute the given values for `x + y` and `x * y`, then evaluate the arithmetic.
  calc
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := h_identity
    _ = 13 ^ 2 - 2 * 24 := by
      simpa [h1, h2]
    _ = 121 := by
      norm_num
