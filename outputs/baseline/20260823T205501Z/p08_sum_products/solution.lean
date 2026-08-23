import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- nonnegativity of a sum of squares
  have h_nonneg :
      0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
    have h1 : 0 ≤ (a - b) ^ 2 := by exact sq_nonneg _
    have h2 : 0 ≤ (b - c) ^ 2 := by exact sq_nonneg _
    have h3 : 0 ≤ (c - a) ^ 2 := by exact sq_nonneg _
    exact add_nonneg (add_nonneg h1 h2) h3
  -- rewrite the sum of squares
  have h_eq :
      (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 =
        2 * ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a)) := by
    ring
  -- deduce the basic quadratic inequality
  have h_sub_nonneg :
      (a + b + c) ^ 2 - 3 * (a * b + b * c + c * a) ≥ 0 := by
    have : 0 ≤ 2 * ((a + b + c) ^ 2 - 3 * (a * b + b * c + c * a)) := by
      simpa [h_eq] using h_nonneg
    nlinarith
  have h3_mul : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 := by
    linarith
  have h_mul : (a * b + b * c + c * a) * 3 ≤ (a + b + c) ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h3_mul
  have hpos : (0 : ℝ) < 3 := by norm_num
  have h_le : a * b + b * c + c * a ≤ (a + b + c) ^ 2 / 3 :=
    (le_div_iff hpos).mpr h_mul
  simpa [h] using h_le
