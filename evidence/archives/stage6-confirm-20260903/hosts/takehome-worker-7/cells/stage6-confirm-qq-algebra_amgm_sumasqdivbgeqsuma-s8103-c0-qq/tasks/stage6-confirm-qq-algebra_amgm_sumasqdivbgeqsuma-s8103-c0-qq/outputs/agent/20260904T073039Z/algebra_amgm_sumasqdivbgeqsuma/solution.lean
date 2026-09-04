import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have hb : 0 < b := h₀.2.1
    have h_eq : a^2 / b + b - 2 * a = (a - b)^2 / b := by
      field_simp [hb.ne']
      ring
    have h_nonneg : 0 ≤ (a - b)^2 / b := by
      apply div_nonneg
      · exact sq_nonneg (a - b)
      · exact le_of_lt hb
    apply le_of_sub_nonneg
    rw [h_eq]
    exact h_nonneg
  
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have hc : 0 < c := h₀.2.2.1
    have h_eq : b^2 / c + c - 2 * b = (b - c)^2 / c := by
      field_simp [hc.ne']
      ring
    have h_nonneg : 0 ≤ (b - c)^2 / c := by
      apply div_nonneg
      · exact sq_nonneg (b - c)
      · exact le_of_lt hc
    apply le_of_sub_nonneg
    rw [h_eq]
    exact h_nonneg
  
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have hd : 0 < d := h₀.2.2.2
    have h_eq : c^2 / d + d - 2 * c = (c - d)^2 / d := by
      field_simp [hd.ne']
      ring
    have h_nonneg : 0 ≤ (c - d)^2 / d := by
      apply div_nonneg
      · exact sq_nonneg (c - d)
      · exact le_of_lt hd
    apply le_of_sub_nonneg
    rw [h_eq]
    exact h_nonneg
  
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have ha : 0 < a := h₀.1
    have h_eq : d^2 / a + a - 2 * d = (d - a)^2 / a := by
      field_simp [ha.ne']
      ring
    have h_nonneg : 0 ≤ (d - a)^2 / a := by
      apply div_nonneg
      · exact sq_nonneg (d - a)
      · exact le_of_lt ha
    apply le_of_sub_nonneg
    rw [h_eq]
    exact h_nonneg
  
  have h₅ : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    calc
      a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) = 
        (a^2 / b + b) + (b^2 / c + c) + (c^2 / d + d) + (d^2 / a + a) := by ring
      _ ≥ 2 * a + 2 * b + 2 * c + 2 * d := by linarith [h₁, h₂, h₃, h₄]
      _ = 2 * (a + b + c + d) := by ring
  
  linarith [h₅]
