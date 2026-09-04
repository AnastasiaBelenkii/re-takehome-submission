import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : 0 < x + y := by linarith [h₀.1, h₀.2.1]
  have h₂ : 0 < y + z := by linarith [h₀.2.1, h₀.2.2]
  have h₃ : 0 < z + x := by linarith [h₀.2.2, h₀.1]
  have h₄ : 0 < x + y + z := by linarith [h₀.1, h₀.2.1, h₀.2.2]
  
  have h₅ : 0 < (x + y) * (y + z) * (z + x) := by positivity
  
  field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne']
  rw [← sub_nonneg]
  ring_nf
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁]
