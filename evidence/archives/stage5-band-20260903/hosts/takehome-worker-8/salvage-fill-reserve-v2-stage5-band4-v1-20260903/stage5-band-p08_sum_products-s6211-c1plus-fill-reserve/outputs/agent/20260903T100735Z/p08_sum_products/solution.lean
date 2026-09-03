import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- Expand (a+b+c)^2 = a^2 + b^2 + c^2 + 2(ab + bc + ca)
  have h1 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
  rw [h] at h1
  have h2 : 9 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by linarith
  -- By Cauchy-Schwarz: a^2 + b^2 + c^2 ≥ (a+b+c)^2/3 = 3
  have h3 : a^2 + b^2 + c^2 ≥ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- From h2 and h3: 2(ab + bc + ca) ≤ 6, so ab + bc + ca ≤ 3
  linarith
