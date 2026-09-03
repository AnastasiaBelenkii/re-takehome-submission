import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  have h_sq_sum : a^2 + b^2 + c^2 ≥ 3 := by
    -- Use the identity (a-b)^2 + (b-c)^2 + (c-a)^2 ≥ 0
    have h1 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by positivity
    have h2 : (a - b)^2 + (b - c)^2 + (c - a)^2 = 2 * (a^2 + b^2 + c^2) - 2 * (a * b + b * c + c * a) := by ring
    have h3 : 2 * (a^2 + b^2 + c^2) - 2 * (a * b + b * c + c * a) ≥ 0 := by linarith
    have h4 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
    have h5 : 9 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by rw [h] at h4; linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h_main : a * b + b * c + c * a ≤ 3 := by
    -- From (a+b+c)^2 = a^2 + b^2 + c^2 + 2(ab + bc + ca)
    have h1 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
    have h2 : 9 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by rw [h] at h1; linarith
    have h3 : 2 * (a * b + b * c + c * a) = 9 - (a^2 + b^2 + c^2) := by linarith
    have h4 : a * b + b * c + c * a = (9 - (a^2 + b^2 + c^2)) / 2 := by linarith
    have h5 : a^2 + b^2 + c^2 ≥ 3 := h_sq_sum
    calc
      a * b + b * c + c * a = (9 - (a^2 + b^2 + c^2)) / 2 := h4
      _ ≤ (9 - 3) / 2 := by gcongr <;> linarith
      _ = 3 := by norm_num
  
  exact h_main
