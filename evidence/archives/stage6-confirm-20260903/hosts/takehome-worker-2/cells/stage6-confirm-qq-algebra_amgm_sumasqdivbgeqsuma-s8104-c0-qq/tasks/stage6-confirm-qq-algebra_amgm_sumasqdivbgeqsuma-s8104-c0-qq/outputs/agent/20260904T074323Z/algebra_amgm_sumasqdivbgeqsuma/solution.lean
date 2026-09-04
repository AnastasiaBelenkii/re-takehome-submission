import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  -- Use AM-GM inequality: x^2/y + y ≥ 2x for positive x, y
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have h₁₀ : 0 < b := h₀.2.1
    have h₁₁ : 0 < a := h₀.1
    have h₁₂ : 0 < a * b := mul_pos h₁₁ h₁₀
    field_simp [h₁₀.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (a - b)]
  
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have h₂₀ : 0 < c := h₀.2.2.1
    have h₂₁ : 0 < b := h₀.2.1
    have h₂₂ : 0 < b * c := mul_pos h₂₁ h₂₀
    field_simp [h₂₀.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (b - c)]
  
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have h₃₀ : 0 < d := h₀.2.2.2
    have h₃₁ : 0 < c := h₀.2.2.1
    have h₃₂ : 0 < c * d := mul_pos h₃₁ h₃₀
    field_simp [h₃₀.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (c - d)]
  
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have h₄₀ : 0 < a := h₀.1
    have h₄₁ : 0 < d := h₀.2.2.2
    have h₄₂ : 0 < d * a := mul_pos h₄₁ h₄₀
    field_simp [h₄₀.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (d - a)]
  
  -- Sum all four inequalities
  have h₅ : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    linarith
  
  -- Subtract (a + b + c + d) from both sides
  linarith
