import Mathlib

open Real

/-- Auxiliary lemma: for positive `x y`, we have `x^2 / y + y ≥ 2 * x`. -/
lemma sq_div_add_self_ge_two_mul (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 / y + y ≥ 2 * x := by
  have hy_nonneg : 0 ≤ y := le_of_lt hy
  have h_nonneg : 0 ≤ (x - y) ^ 2 := by
    exact pow_two_nonneg _
  have h_eq : (x ^ 2 + y ^ 2 - 2 * x * y) = (x - y) ^ 2 := by
    ring
  have h1 : 0 ≤ x ^ 2 + y ^ 2 - 2 * x * y := by
    simpa [h_eq] using h_nonneg
  have h2 : 0 ≤ (x ^ 2 + y ^ 2 - 2 * x * y) / y := by
    exact div_nonneg h1 hy_nonneg
  have h3 : (x ^ 2 + y ^ 2 - 2 * x * y) / y = x ^ 2 / y + y - 2 * x := by
    field_simp [hy.ne']
  have : x ^ 2 / y + y - 2 * x ≥ 0 := by
    simpa [h3] using h2
  linarith

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  -- extract positivity hypotheses
  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2.1
  have hc : 0 < c := h₀.2.2.1
  have hd : 0 < d := h₀.2.2.2

  -- apply the auxiliary lemma to each pair
  have h1 := sq_div_add_self_ge_two_mul a b ha hb
  have h2 := sq_div_add_self_ge_two_mul b c hb hc
  have h3 := sq_div_add_self_ge_two_mul c d hc hd
  have h4 := sq_div_add_self_ge_two_mul d a hd ha

  -- sum the four inequalities
  have hsum₁ :
      a ^ 2 / b + b + b ^ 2 / c + c + c ^ 2 / d + d + d ^ 2 / a + a ≥
        2 * a + 2 * b + 2 * c + 2 * d := by
    linarith [h1, h2, h3, h4]

  have hsum₂ :
      a ^ 2 / b + b + b ^ 2 / c + c + c ^ 2 / d + d + d ^ 2 / a + a ≥
        2 * (a + b + c + d) := by
    simpa [mul_add, add_mul, two_mul, add_comm, add_left_comm, add_assoc] using hsum₁

  have hsum' :
      a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a + (a + b + c + d) ≥
        2 * (a + b + c + d) := by
    simpa [add_comm, add_left_comm, add_assoc] using hsum₂

  -- conclude the desired inequality
  have : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    linarith [hsum']
  exact this
