import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p2
  (x p : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < p ∧ p < 15)
  (h₁ : p ≤ x ∧ x ≤ 15)
  (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
  15 ≤ f x := by
  have hp_pos : 0 < p := h₀.1
  have hx_le_15 : x ≤ 15 := h₁.2
  have px_le_x : p ≤ x := h₁.1
  
  have h₃ : abs (x - p) = x - p := by
    rw [abs_of_nonneg]
    linarith [px_le_x]
  
  have h₄ : abs (x - 15) = 15 - x := by
    have h₄_le : x - 15 ≤ 0 := by linarith [hx_le_15]
    rw [abs_of_nonpos h₄_le]
    ring
  
  have h₅ : abs (x - p - 15) = 15 + p - x := by
    have h₅_le : x - p - 15 ≤ 0 := by linarith [hx_le_15, hp_pos]
    rw [abs_of_nonpos h₅_le]
    ring
  
  rw [h₂, h₃, h₄, h₅]
  linarith [hx_le_15]
