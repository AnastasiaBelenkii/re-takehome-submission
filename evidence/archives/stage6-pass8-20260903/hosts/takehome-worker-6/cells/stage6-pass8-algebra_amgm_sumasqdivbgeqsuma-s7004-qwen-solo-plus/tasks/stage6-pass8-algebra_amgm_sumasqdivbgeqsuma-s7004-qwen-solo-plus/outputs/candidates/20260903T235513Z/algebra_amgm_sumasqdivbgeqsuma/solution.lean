import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have hb : 0 < b := h₀.2.1
    have ha : 0 < a := h₀.1
    have h_sq : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
    have h_eq : a^2 / b + b - 2 * a = (a - b)^2 / b := by
      field_simp [hb.ne']
      ring
    have h_nonneg : 0 ≤ (a - b)^2 / b := div_nonneg h_sq (le_of_lt hb)
    have h_diff : a^2 / b + b - 2 * a ≥ 0 := by
      rw [h_eq]
      exact h_nonneg
    linarith
  
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have hc : 0 < c := h₀.2.2.1
    have hb : 0 < b := h₀.2.1
    have h_sq : 0 ≤ (b - c)^2 := sq_nonneg (b - c)
    have h_eq : b^2 / c + c - 2 * b = (b - c)^2 / c := by
      field_simp [hc.ne']
      ring
    have h_nonneg : 0 ≤ (b - c)^2 / c := div_nonneg h_sq (le_of_lt hc)
    have h_diff : b^2 / c + c - 2 * b ≥ 0 := by
      rw [h_eq]
      exact h_nonneg
    linarith
  
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have hd : 0 < d := h₀.2.2.2
    have hc : 0 < c := h₀.2.2.1
    have h_sq : 0 ≤ (c - d)^2 := sq_nonneg (c - d)
    have h_eq : c^2 / d + d - 2 * c = (c - d)^2 / d := by
      field_simp [hd.ne']
      ring
    have h_nonneg : 0 ≤ (c - d)^2 / d := div_nonneg h_sq (le_of_lt hd)
    have h_diff : c^2 / d + d - 2 * c ≥ 0 := by
      rw [h_eq]
      exact h_nonneg
    linarith
  
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have ha : 0 < a := h₀.1
    have hd : 0 < d := h₀.2.2.2
    have h_sq : 0 ≤ (d - a)^2 := sq_nonneg (d - a)
    have h_eq : d^2 / a + a - 2 * d = (d - a)^2 / a := by
      field_simp [ha.ne']
      ring
    have h_nonneg : 0 ≤ (d - a)^2 / a := div_nonneg h_sq (le_of_lt ha)
    have h_diff : d^2 / a + a - 2 * d ≥ 0 := by
      rw [h_eq]
      exact h_nonneg
    linarith
  
  linarith
