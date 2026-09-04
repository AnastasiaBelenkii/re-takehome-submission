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
  have hxy : 0 < x + y := by linarith
  have hyz : 0 < y + z := by linarith
  have hzx : 0 < z + x := by linarith
  have hxyz : 0 < x + y + z := by linarith
  
  -- Prove the polynomial inequality equivalent to the statement
  have h_poly : 9 * (x + y) * (y + z) * (z + x) ≤ 
                (x + y + z) * (2 * (y + z) * (z + x) + 2 * (x + y) * (z + x) + 2 * (x + y) * (y + z)) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
               mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
               mul_pos hxy hyz, mul_pos hyz hzx, mul_pos hzx hxy,
               sq_nonneg (x + y - 2 * z), sq_nonneg (y + z - 2 * x), sq_nonneg (z + x - 2 * y)]
  
  -- Convert the polynomial inequality back to the fraction inequality
  have h_final : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    have h₁ : 0 < (x + y) * (y + z) * (z + x) := by positivity
    have h₂ : 0 < x + y + z := by linarith
    
    -- Calculate the difference and show it is non-positive
    have h_diff : 9 / (x + y + z) - (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) ≤ 0 := by
      have h₃ : 9 / (x + y + z) - (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) = 
                (9 * (x + y) * (y + z) * (z + x) - (x + y + z) * (2 * (y + z) * (z + x) + 2 * (x + y) * (z + x) + 2 * (x + y) * (y + z))) / 
                ((x + y + z) * (x + y) * (y + z) * (z + x)) := by
        field_simp [hxy.ne', hyz.ne', hzx.ne', hxyz.ne']
        <;> ring
      rw [h₃]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Numerator is non-positive due to h_poly
        linarith [h_poly]
      · -- Denominator is positive
        positivity
    linarith
  
  exact h_final
