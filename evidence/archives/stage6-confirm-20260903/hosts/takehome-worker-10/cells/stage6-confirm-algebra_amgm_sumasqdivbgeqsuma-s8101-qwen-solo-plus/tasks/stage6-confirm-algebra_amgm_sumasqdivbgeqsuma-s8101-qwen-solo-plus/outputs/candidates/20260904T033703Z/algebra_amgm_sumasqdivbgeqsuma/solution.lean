import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have hb : 0 < b := h₀.2.1
    have h_sq : (a - b)^2 ≥ 0 := sq_nonneg (a - b)
    have h_main : a^2 / b + b - 2 * a = (a - b)^2 / b := by
      field_simp [hb.ne']
      ring
    have h_div_nonneg : (a - b)^2 / b ≥ 0 := by
      apply div_nonneg
      · exact h_sq
      · exact le_of_lt hb
    linarith
  
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have hc : 0 < c := h₀.2.2.1
    have h_sq : (b - c)^2 ≥ 0 := sq_nonneg (b - c)
    have h_main : b^2 / c + c - 2 * b = (b - c)^2 / c := by
      field_simp [hc.ne']
      ring
    have h_div_nonneg : (b - c)^2 / c ≥ 0 := by
      apply div_nonneg
      · exact h_sq
      · exact le_of_lt hc
    linarith
  
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have hd : 0 < d := h₀.2.2.2
    have h_sq : (c - d)^2 ≥ 0 := sq_nonneg (c - d)
    have h_main : c^2 / d + d - 2 * c = (c - d)^2 / d := by
      field_simp [hd.ne']
      ring
    have h_div_nonneg : (c - d)^2 / d ≥ 0 := by
      apply div_nonneg
      · exact h_sq
      · exact le_of_lt hd
    linarith
  
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have ha : 0 < a := h₀.1
    have h_sq : (d - a)^2 ≥ 0 := sq_nonneg (d - a)
    have h_main : d^2 / a + a - 2 * d = (d - a)^2 / a := by
      field_simp [ha.ne']
      ring
    have h_div_nonneg : (d - a)^2 / a ≥ 0 := by
      apply div_nonneg
      · exact h_sq
      · exact le_of_lt ha
    linarith
  
  have h_sum : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    linarith [h₁, h₂, h₃, h₄]
  
  have h_final : a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
    linarith [h_sum]
  
  exact h_final
