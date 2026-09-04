import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have h₁₀ : 0 < b := h₀.2.1
    have h₁₁ : 0 < a := h₀.1
    have h₁₂ : (a - b)^2 / b ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (a - b)
      · linarith
    have h₁₃ : (a - b)^2 / b = a^2 / b + b - 2 * a := by
      field_simp [h₁₀.ne']
      ring
    linarith
  
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have h₂₀ : 0 < c := h₀.2.2.1
    have h₂₁ : 0 < b := h₀.2.1
    have h₂₂ : (b - c)^2 / c ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (b - c)
      · linarith
    have h₂₃ : (b - c)^2 / c = b^2 / c + c - 2 * b := by
      field_simp [h₂₀.ne']
      ring
    linarith
  
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have h₃₀ : 0 < d := h₀.2.2.2
    have h₃₁ : 0 < c := h₀.2.2.1
    have h₃₂ : (c - d)^2 / d ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (c - d)
      · linarith
    have h₃₃ : (c - d)^2 / d = c^2 / d + d - 2 * c := by
      field_simp [h₃₀.ne']
      ring
    linarith
  
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have h₄₀ : 0 < a := h₀.1
    have h₄₁ : 0 < d := h₀.2.2.2
    have h₄₂ : (d - a)^2 / a ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (d - a)
      · linarith
    have h₄₃ : (d - a)^2 / a = d^2 / a + a - 2 * d := by
      field_simp [h₄₀.ne']
      ring
    linarith
  
  -- Sum all inequalities
  have h₅ : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    linarith [h₁, h₂, h₃, h₄]
  
  -- Subtract (a + b + c + d) from both sides
  linarith
