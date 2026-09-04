import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3*z := by
    rw [eq_sub_of_add_eq h₀]
  
  rw [h₂] at h₁
  ring_nf at h₁
  -- h₁ is now 30 - 14*z = -68 (possibly with z*14)
  
  have h₃ : z = 7 := by
    have h₄ : 14 * z = 98 := by
      rw [← sub_eq_zero] at h₁
      ring_nf at h₁
      -- h₁ is now 98 - 14*z = 0 or 98 - z*14 = 0
      rw [mul_comm] at h₁
      rw [sub_eq_zero] at h₁
      -- h₁ is now 98 = 14*z
      rw [eq_comm] at h₁
      exact h₁
    
    apply mul_left_cancel₀ (show (14 : ℂ) ≠ 0 by norm_num)
    rw [h₄]
    norm_num
  
  have h₄ : f = -10 := by
    rw [h₂, h₃]
    norm_num
  
  exact ⟨h₄, h₃⟩
