import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  -- Use AM-GM inequality: x^2/y + y ≥ 2x for positive x, y
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have h₁' : 0 < b := h₀.2.1
    have h₂ : 0 < a := h₀.1
    have h₃ : 0 < a * b := mul_pos h₂ h₁'
    have h₄ : a^2 + b^2 ≥ 2 * a * b := by
      nlinarith [sq_nonneg (a - b)]
    calc
      a^2 / b + b = (a^2 + b^2) / b := by field_simp [h₁'.ne']
      _ ≥ (2 * a * b) / b := by gcongr
      _ = 2 * a := by field_simp [h₁'.ne']
  
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have h₂' : 0 < c := h₀.2.2.1
    have h₃ : 0 < b := h₀.2.1
    have h₄ : 0 < b * c := mul_pos h₃ h₂'
    have h₅ : b^2 + c^2 ≥ 2 * b * c := by
      nlinarith [sq_nonneg (b - c)]
    calc
      b^2 / c + c = (b^2 + c^2) / c := by field_simp [h₂'.ne']
      _ ≥ (2 * b * c) / c := by gcongr
      _ = 2 * b := by field_simp [h₂'.ne']
  
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have h₃' : 0 < d := h₀.2.2.2
    have h₄ : 0 < c := h₀.2.2.1
    have h₅ : 0 < c * d := mul_pos h₄ h₃'
    have h₆ : c^2 + d^2 ≥ 2 * c * d := by
      nlinarith [sq_nonneg (c - d)]
    calc
      c^2 / d + d = (c^2 + d^2) / d := by field_simp [h₃'.ne']
      _ ≥ (2 * c * d) / d := by gcongr
      _ = 2 * c := by field_simp [h₃'.ne']
  
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have h₄' : 0 < a := h₀.1
    have h₅ : 0 < d := h₀.2.2.2
    have h₆ : 0 < d * a := mul_pos h₅ h₄'
    have h₇ : d^2 + a^2 ≥ 2 * d * a := by
      nlinarith [sq_nonneg (d - a)]
    calc
      d^2 / a + a = (d^2 + a^2) / a := by field_simp [h₄'.ne']
      _ ≥ (2 * d * a) / a := by gcongr
      _ = 2 * d := by field_simp [h₄'.ne']
  
  -- Sum all four inequalities
  have h₅ : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    linarith
  
  -- Subtract (a + b + c + d) from both sides
  linarith
