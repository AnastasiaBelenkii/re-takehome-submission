import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3 * z := by
    calc
      f = (f + 3 * z) - 3 * z := by ring
      _ = 11 - 3 * z := by rw [h₀]
  
  rw [h₂] at h₁
  ring_nf at h₁
  -- h₁ : 30 - z * 14 = -68
  
  have h_z_val : 14 * z = 98 := by
    calc
      14 * z = 14 * z - 30 + 30 := by ring
      _ = -(30 - 14 * z) + 30 := by ring
      _ = -(30 - z * 14) + 30 := by ring_nf
      _ = -(-68) + 30 := by rw [← h₁]
      _ = 98 := by ring
  
  have h₃ : z = 7 := by
    apply mul_left_cancel₀ (show (14 : ℂ) ≠ 0 by norm_num)
    rw [h_z_val]
    norm_num
  
  have h₄ : f = -10 := by
    rw [h₂, h₃]
    norm_num
  
  exact ⟨h₄, h₃⟩
