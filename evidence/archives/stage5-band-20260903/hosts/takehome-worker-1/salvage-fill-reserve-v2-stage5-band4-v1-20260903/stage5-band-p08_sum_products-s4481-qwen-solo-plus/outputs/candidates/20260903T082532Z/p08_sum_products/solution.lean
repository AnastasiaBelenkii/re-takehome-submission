import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- Use the identity (a+b+c)² = a² + b² + c² + 2(ab + bc + ca)
  -- Since a + b + c = 3, we have 9 = a² + b² + c² + 2(ab + bc + ca)
  -- So ab + bc + ca = (9 - (a² + b² + c²))/2
  -- By Cauchy-Schwarz, a² + b² + c² ≥ (a+b+c)²/3 = 9/3 = 3
  -- Therefore ab + bc + ca ≤ (9-3)/2 = 3
  have h1 : a^2 + b^2 + c^2 ≥ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h2 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
    ring
  rw [h] at h2
  have h3 : 9 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by linarith
  have h4 : a * b + b * c + c * a = (9 - (a^2 + b^2 + c^2)) / 2 := by linarith
  rw [h4]
  linarith
