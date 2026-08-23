import Mathlib

/-- Real numbers `x` and `y` satisfy `x + y = 13` and `x * y = 24`.
Show that `x ^ 2 + y ^ 2 = 121`. -/
theorem p04_sum_sq (x y : ℝ) (h1 : x + y = 13) (h2 : x * y = 24) : x ^ 2 + y ^ 2 = 121 := by
  calc
    x ^ 2 + y ^ 2
        = (x + y) ^ 2 - 2 * (x * y) := by
          have h : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * (x * y) := by
            ring
          linarith
    _ = (13 : ℝ) ^ 2 - 2 * 24 := by
          simpa [h1, h2]
    _ = 121 := by
          norm_num
