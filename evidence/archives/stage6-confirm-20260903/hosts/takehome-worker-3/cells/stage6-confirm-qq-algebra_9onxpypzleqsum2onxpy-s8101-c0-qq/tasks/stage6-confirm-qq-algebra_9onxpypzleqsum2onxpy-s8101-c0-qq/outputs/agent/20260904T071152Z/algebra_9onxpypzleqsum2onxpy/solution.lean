import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have hx : 0 < x := h₀.1
  have hy : 0 < y := h₀.2.1
  have hz : 0 < z := h₀.2.2
  
  have hxy : 0 < x + y := add_pos hx hy
  have hyz : 0 < y + z := add_pos hy hz
  have hzx : 0 < z + x := add_pos hz hx
  have hxyz : 0 < x + y + z := add_pos (add_pos hx hy) hz
  
  have h_denom_pos : 0 < (x + y) * (y + z) * (z + x) * (x + y + z) := by positivity
  
  have h_main : 0 ≤ 2 * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) * (x + y + z) - 9 * (x + y) * (y + z) * (z + x) := by
    ring_nf
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hxy hyz, mul_pos hyz hzx, mul_pos hzx hxy]
  
  have h_rhs_common : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) = 
    2 * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) / ((x + y) * (y + z) * (z + x)) := by
    field_simp [hxy.ne', hyz.ne', hzx.ne']
    <;> ring
    <;> field_simp [hxy.ne', hyz.ne', hzx.ne']
    <;> ring
  
  have h_lhs_common : 9 / (x + y + z) = 
    9 * (x + y) * (y + z) * (z + x) / ((x + y) * (y + z) * (z + x) * (x + y + z)) := by
    field_simp [hxy.ne', hyz.ne', hzx.ne', hxyz.ne']
    <;> ring
    <;> field_simp [hxy.ne', hyz.ne', hzx.ne', hxyz.ne']
    <;> ring
  
  have h_diff : 0 ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) - 9 / (x + y + z) := by
    rw [h_rhs_common, h_lhs_common]
    have h_num : 0 ≤ 2 * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) * (x + y + z) - 9 * (x + y) * (y + z) * (z + x) := h_main
    have h_denom : 0 < (x + y) * (y + z) * (z + x) * (x + y + z) := h_denom_pos
    
    have h₁ : 0 ≤ (2 * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) * (x + y + z) - 9 * (x + y) * (y + z) * (z + x)) / ((x + y) * (y + z) * (z + x) * (x + y + z)) := by
      apply div_nonneg
      · linarith
      · linarith
    
    -- Show that the simplified expression equals our target
    have h₂ : (2 * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) / ((x + y) * (y + z) * (z + x))) - 
              (9 * (x + y) * (y + z) * (z + x) / ((x + y) * (y + z) * (z + x) * (x + y + z))) = 
              (2 * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) * (x + y + z) - 9 * (x + y) * (y + z) * (z + x)) / ((x + y) * (y + z) * (z + x) * (x + y + z)) := by
      field_simp [hxy.ne', hyz.ne', hzx.ne', hxyz.ne']
      <;> ring
      <;> field_simp [hxy.ne', hyz.ne', hzx.ne', hxyz.ne']
      <;> ring
    
    rw [h₂]
    exact h₁
  
  linarith [h_diff]
