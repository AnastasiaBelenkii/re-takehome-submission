import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  -- Use the fact that (x - y)^2 ≥ 0 implies x^2/y + y ≥ 2x for positive x, y
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have h₁' : 0 < b := h₀.2.1
    have h₁'' : 0 < a := h₀.1
    field_simp [h₁'.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (a - b)]
  
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have h₂' : 0 < c := h₀.2.2.1
    have h₂'' : 0 < b := h₀.2.1
    field_simp [h₂'.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (b - c)]
  
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have h₃' : 0 < d := h₀.2.2.2
    have h₃'' : 0 < c := h₀.2.2.1
    field_simp [h₃'.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (c - d)]
  
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have h₄' : 0 < a := h₀.1
    have h₄'' : 0 < d := h₀.2.2.2
    field_simp [h₄'.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (d - a)]
  
  -- Sum all four inequalities
  have h₅ : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    linarith
  
  -- Subtract (a + b + c + d) from both sides
  linarith
