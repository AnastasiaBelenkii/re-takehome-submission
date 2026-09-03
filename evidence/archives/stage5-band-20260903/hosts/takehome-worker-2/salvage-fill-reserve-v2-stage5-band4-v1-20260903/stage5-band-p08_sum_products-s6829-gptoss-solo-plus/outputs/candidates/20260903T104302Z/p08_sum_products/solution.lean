import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- First prove the classical inequality `3·(ab+bc+ca) ≤ (a+b+c)²`.
  have hineq : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
    -- Rewrite the difference as a sum of squares.
    have h_eq :
        (a + b + c) ^ 2 - 3 * (a * b + b * c + c * a) =
          ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2 := by
      ring
    -- The right‑hand side is non‑negative.
    have h_nonneg :
        0 ≤ ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2 := by
      have hsum : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
        have h1 : 0 ≤ (a - b) ^ 2 := by exact sq_nonneg _
        have h2 : 0 ≤ (b - c) ^ 2 := by exact sq_nonneg _
        have h3 : 0 ≤ (c - a) ^ 2 := by exact sq_nonneg _
        exact add_nonneg (add_nonneg h1 h2) h3
      have hpos : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact div_nonneg hsum (le_of_lt hpos)
    have h_sub_nonneg :
        0 ≤ (a + b + c) ^ 2 - 3 * (a * b + b * c + c * a) := by
      simpa [h_eq] using h_nonneg
    -- From `0 ≤ X - Y` we obtain `Y ≤ X`.
    have : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 := by
      linarith
    exact this
  -- Substitute the hypothesis `a + b + c = 3`.
  have hineq' : 3 * (a * b + b * c + c * a) ≤ (3 : ℝ) ^ 2 := by
    simpa [h] using hineq
  -- Rewrite the right‑hand side as `3 * 3`.
  have hineq'' : 3 * (a * b + b * c + c * a) ≤ 3 * 3 := by
    simpa [pow_two] using hineq'
  -- Cancel the positive factor `3`.
  have hpos : (0 : ℝ) < 3 := by norm_num
  have : a * b + b * c + c * a ≤ 3 :=
    (le_of_mul_le_mul_left hineq'' hpos)
  exact this
