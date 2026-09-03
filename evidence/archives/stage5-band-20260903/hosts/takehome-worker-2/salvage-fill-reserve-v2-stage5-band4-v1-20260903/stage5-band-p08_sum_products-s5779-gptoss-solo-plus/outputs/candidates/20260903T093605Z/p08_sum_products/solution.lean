import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- First we show `a^2 + b^2 + c^2 ≥ a*b + b*c + c*a`.
  have h1 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h_nonneg : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
      have h1 : 0 ≤ (a - b) ^ 2 := by exact sq_nonneg _
      have h2 : 0 ≤ (b - c) ^ 2 := by exact sq_nonneg _
      have h3 : 0 ≤ (c - a) ^ 2 := by exact sq_nonneg _
      linarith
    have h_eq :
        (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 =
          2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
      ring
    have : 0 ≤ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
      simpa [h_eq] using h_nonneg
    linarith
  -- From this we obtain `(a+b+c)^2 ≥ 3*(ab+bc+ca)`.
  have h2 : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
    have h_eq : (a + b + c) ^ 2 =
        a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
      ring
    have : a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) ≥
        3 * (a * b + b * c + c * a) := by
      linarith
    simpa [h_eq] using this
  -- Substitute `a + b + c = 3`.
  have h3 : (3 : ℝ) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
    simpa [h] using h2
  -- Simplify the left‑hand side.
  have h4 : (3 : ℝ) * 3 ≥ 3 * (a * b + b * c + c * a) := by
    simpa [pow_two] using h3
  -- Divide by the positive constant `3`.
  have : a * b + b * c + c * a ≤ 3 := by
    linarith
  exact this
