import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩

  -- auxiliary inequalities `2 * x ≤ x^2 / y + y`
  have h1' : 2 * a ≤ a ^ 2 / b + b := by
    have hbpos : 0 < b := hb
    have h_eq : a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
      field_simp [hb.ne']
      ring
    have h_nonneg : 0 ≤ (a - b) ^ 2 / b := by
      have h_sq : 0 ≤ (a - b) ^ 2 := by
        have : (a - b) ^ 2 = (a - b) * (a - b) := by ring
        have : 0 ≤ (a - b) * (a - b) := mul_self_nonneg (a - b)
        simpa [pow_two] using this
      exact div_nonneg h_sq (le_of_lt hbpos)
    have : a ^ 2 / b + b - 2 * a ≥ 0 := by
      simpa [h_eq] using h_nonneg
    linarith

  have h2' : 2 * b ≤ b ^ 2 / c + c := by
    have hcpos : 0 < c := hc
    have h_eq : b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
      field_simp [hc.ne']
      ring
    have h_nonneg : 0 ≤ (b - c) ^ 2 / c := by
      have h_sq : 0 ≤ (b - c) ^ 2 := by
        have : (b - c) ^ 2 = (b - c) * (b - c) := by ring
        have : 0 ≤ (b - c) * (b - c) := mul_self_nonneg (b - c)
        simpa [pow_two] using this
      exact div_nonneg h_sq (le_of_lt hcpos)
    have : b ^ 2 / c + c - 2 * b ≥ 0 := by
      simpa [h_eq] using h_nonneg
    linarith

  have h3' : 2 * c ≤ c ^ 2 / d + d := by
    have hdpos : 0 < d := hd
    have h_eq : c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
      field_simp [hd.ne']
      ring
    have h_nonneg : 0 ≤ (c - d) ^ 2 / d := by
      have h_sq : 0 ≤ (c - d) ^ 2 := by
        have : (c - d) ^ 2 = (c - d) * (c - d) := by ring
        have : 0 ≤ (c - d) * (c - d) := mul_self_nonneg (c - d)
        simpa [pow_two] using this
      exact div_nonneg h_sq (le_of_lt hdpos)
    have : c ^ 2 / d + d - 2 * c ≥ 0 := by
      simpa [h_eq] using h_nonneg
    linarith

  have h4' : 2 * d ≤ d ^ 2 / a + a := by
    have hapos : 0 < a := ha
    have h_eq : d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
      field_simp [ha.ne']
      ring
    have h_nonneg : 0 ≤ (d - a) ^ 2 / a := by
      have h_sq : 0 ≤ (d - a) ^ 2 := by
        have : (d - a) ^ 2 = (d - a) * (d - a) := by ring
        have : 0 ≤ (d - a) * (d - a) := mul_self_nonneg (d - a)
        simpa [pow_two] using this
      exact div_nonneg h_sq (le_of_lt hapos)
    have : d ^ 2 / a + a - 2 * d ≥ 0 := by
      simpa [h_eq] using h_nonneg
    linarith

  -- sum the four auxiliary inequalities
  have hsum :
      2 * (a + b + c + d) ≤
        (a ^ 2 / b + b) + (b ^ 2 / c + c) + (c ^ 2 / d + d) + (d ^ 2 / a + a) := by
    have h12 := add_le_add h1' h2'
    have h34 := add_le_add h3' h4'
    have htotal := add_le_add h12 h34
    simpa [add_comm, add_left_comm, add_assoc, mul_add, add_mul, two_mul] using htotal

  have h_eq_sum :
      (a ^ 2 / b + b) + (b ^ 2 / c + c) + (c ^ 2 / d + d) + (d ^ 2 / a + a) =
        (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) := by
    ring

  have : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    have : 2 * (a + b + c + d) ≤
        (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) := by
      simpa [h_eq_sum, mul_add, add_mul, two_mul] using hsum
    linarith

  exact this
