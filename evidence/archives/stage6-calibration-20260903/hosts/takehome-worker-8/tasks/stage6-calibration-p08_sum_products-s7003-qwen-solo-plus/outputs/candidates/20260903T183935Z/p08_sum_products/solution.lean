import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- Use the identity (a-b)^2 + (b-c)^2 + (c-a)^2 ≥ 0
  -- This expands to 2(a^2 + b^2 + c^2) - 2(ab + bc + ca) ≥ 0
  -- So a^2 + b^2 + c^2 ≥ ab + bc + ca
  have h1 : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  -- From (a+b+c)^2 = a^2 + b^2 + c^2 + 2(ab + bc + ca)
  -- We get 9 = a^2 + b^2 + c^2 + 2(ab + bc + ca)
  have h2 : a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) = 9 := by
    calc
      a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) = (a + b + c)^2 := by ring
      _ = 3^2 := by rw [h]
      _ = 9 := by norm_num
  
  -- Combine h1 and h2 to get the result
  have h3 : 3 * (a * b + b * c + c * a) ≤ 9 := by
    linarith
  
  linarith
