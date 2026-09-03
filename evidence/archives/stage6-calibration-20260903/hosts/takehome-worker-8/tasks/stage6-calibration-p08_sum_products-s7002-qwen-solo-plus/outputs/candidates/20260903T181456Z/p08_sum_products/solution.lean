import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- Use the identity (a+b+c)² = a² + b² + c² + 2(ab + bc + ca)
  -- Since a + b + c = 3, we have 9 = a² + b² + c² + 2(ab + bc + ca)
  -- So ab + bc + ca = (9 - (a² + b² + c²))/2
  -- By Cauchy-Schwarz: 3(a² + b² + c²) ≥ (a + b + c)² = 9, so a² + b² + c² ≥ 3
  have h1 : a^2 + b^2 + c^2 ≥ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- From the identity and h1, we get ab + bc + ca ≤ 3
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
