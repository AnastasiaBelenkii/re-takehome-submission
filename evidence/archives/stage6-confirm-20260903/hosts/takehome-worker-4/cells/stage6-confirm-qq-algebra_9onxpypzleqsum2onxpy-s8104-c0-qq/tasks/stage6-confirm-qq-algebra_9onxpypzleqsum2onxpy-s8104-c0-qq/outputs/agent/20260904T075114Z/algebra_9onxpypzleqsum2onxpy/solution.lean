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
  
  have h_denom_pos : 0 < (x + y) * (y + z) * (z + x) * (x + y + z) := by positivity
  
  have h_main : 0 ≤ 2 * ((y + z + (x + y)) * (z + x) + (x + y) * (y + z)) * (x + y + z) - (x + y) * (y + z) * (z + x) * 9 := by
    ring_nf
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₃ h₁]
  
  have h_diff_nonneg : 0 ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) - 9 / (x + y + z) := by
    have h_num : 0 ≤ 2 * ((y + z + (x + y)) * (z + x) + (x + y) * (y + z)) * (x + y + z) - (x + y) * (y + z) * (z + x) * 9 := h_main
    have h_denom : 0 < (x + y) * (y + z) * (z + x) * (x + y + z) := h_denom_pos
    
    have h_frac : (2 / (x + y) + 2 / (y + z) + 2 / (z + x) - 9 / (x + y + z)) = 
      (2 * ((y + z + (x + y)) * (z + x) + (x + y) * (y + z)) * (x + y + z) - (x + y) * (y + z) * (z + x) * 9) / ((x + y) * (y + z) * (z + x) * (x + y + z)) := by
      field_simp [h₄.ne', h₅.ne', h₆.ne', h₇.ne']
      <;> ring_nf
      <;> field_simp [h₄.ne', h₅.ne', h₆.ne', h₇.ne']
      <;> ring_nf
    
    rw [h_frac]
    apply div_nonneg
    · exact h_num
    · positivity
  
  -- Convert the non-negativity of the difference to the desired inequality
  have h_final : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    linarith
  
  exact h_final
