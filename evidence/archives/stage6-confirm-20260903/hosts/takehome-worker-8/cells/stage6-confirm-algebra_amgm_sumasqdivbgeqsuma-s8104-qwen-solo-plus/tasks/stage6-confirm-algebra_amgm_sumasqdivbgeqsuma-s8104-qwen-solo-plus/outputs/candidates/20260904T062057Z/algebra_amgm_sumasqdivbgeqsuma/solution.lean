import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : 0 < a := h₀.1
  have h₂ : 0 < b := h₀.2.1
  have h₃ : 0 < c := h₀.2.2.1
  have h₄ : 0 < d := h₀.2.2.2
  
  -- Apply AM-GM to each pair: x²/y + y ≥ 2x for positive x, y
  have h₅ : a^2 / b + b ≥ 2 * a := by
    have h₅₁ : 0 < b := h₂
    have h₅₂ : 0 < a := h₁
    have h₅₃ : a^2 / b + b - 2 * a = (a - b)^2 / b := by
      field_simp [h₅₁.ne']
      ring
    have h₅₄ : (a - b)^2 / b ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (a - b)
      · linarith
    linarith
  
  have h₆ : b^2 / c + c ≥ 2 * b := by
    have h₆₁ : 0 < c := h₃
    have h₆₂ : 0 < b := h₂
    have h₆₃ : b^2 / c + c - 2 * b = (b - c)^2 / c := by
      field_simp [h₆₁.ne']
      ring
    have h₆₄ : (b - c)^2 / c ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (b - c)
      · linarith
    linarith
  
  have h₇ : c^2 / d + d ≥ 2 * c := by
    have h₇₁ : 0 < d := h₄
    have h₇₂ : 0 < c := h₃
    have h₇₃ : c^2 / d + d - 2 * c = (c - d)^2 / d := by
      field_simp [h₇₁.ne']
      ring
    have h₇₄ : (c - d)^2 / d ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (c - d)
      · linarith
    linarith
  
  have h₈ : d^2 / a + a ≥ 2 * d := by
    have h₈₁ : 0 < a := h₁
    have h₈₂ : 0 < d := h₄
    have h₈₃ : d^2 / a + a - 2 * d = (d - a)^2 / a := by
      field_simp [h₈₁.ne']
      ring
    have h₈₄ : (d - a)^2 / a ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (d - a)
      · linarith
    linarith
  
  -- Sum all four inequalities
  have h₉ : (a^2 / b + b) + (b^2 / c + c) + (c^2 / d + d) + (d^2 / a + a) ≥ 2 * a + 2 * b + 2 * c + 2 * d := by
    linarith [h₅, h₆, h₇, h₈]
  
  -- Rearrange to get the desired inequality
  have h₁₀ : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    ring_nf at h₉ ⊢
    linarith
  
  linarith
