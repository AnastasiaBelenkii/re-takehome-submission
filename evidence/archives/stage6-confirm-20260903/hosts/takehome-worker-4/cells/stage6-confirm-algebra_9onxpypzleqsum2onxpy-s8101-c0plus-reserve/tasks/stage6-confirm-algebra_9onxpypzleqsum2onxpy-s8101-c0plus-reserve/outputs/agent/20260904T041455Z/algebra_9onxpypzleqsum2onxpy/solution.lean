import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : 0 < x := h₀.1
  have h₂ : 0 < y := h₀.2.1
  have h₃ : 0 < z := h₀.2.2
  have h₄ : 0 < x + y := add_pos h₁ h₂
  have h₅ : 0 < y + z := add_pos h₂ h₃
  have h₆ : 0 < z + x := add_pos h₃ h₁
  have h₇ : 0 < x + y + z := add_pos (add_pos h₁ h₂) h₃
  
  have h_denom_pos : 0 < (x + y + z) * (x + y) * (y + z) * (z + x) := by positivity
  
  have h_poly : 9 * (x + y) * (y + z) * (z + x) ≤ 2 * (x + y + z) * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) := by
    ring_nf
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  calc
    9 / (x + y + z) = (9 * (x + y) * (y + z) * (z + x)) / ((x + y + z) * (x + y) * (y + z) * (z + x)) := by
      field_simp [h₄.ne', h₅.ne', h₆.ne', h₇.ne']
      <;> ring
    _ ≤ (2 * (x + y + z) * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z))) / ((x + y + z) * (x + y) * (y + z) * (z + x)) := by
      gcongr
      <;> assumption
    _ = 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
      field_simp [h₄.ne', h₅.ne', h₆.ne', h₇.ne']
      <;> ring
