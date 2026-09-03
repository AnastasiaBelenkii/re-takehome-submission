import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- Use the identity (a+b+c)² = a² + b² + c² + 2(ab + bc + ca)
  have h1 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
    ring
  rw [h] at h1
  -- So 9 = a² + b² + c² + 2(ab + bc + ca)
  -- We need to show a² + b² + c² ≥ 3 using Cauchy-Schwarz
  have h2 : a^2 + b^2 + c^2 ≥ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- From h1: 9 = a² + b² + c² + 2(ab + bc + ca) ≥ 3 + 2(ab + bc + ca)
  -- So 6 ≥ 2(ab + bc + ca), hence ab + bc + ca ≤ 3
  linarith
