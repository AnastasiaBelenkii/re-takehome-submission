import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h_f : f = 11 - 3 * z := by
    rw [← sub_eq_zero] at h₀
    rw [← sub_eq_zero]
    ring_nf at h₀
    ring_nf
    exact h₀
  
  rw [h_f] at h₁
  ring_nf at h₁
  
  have h_z : z = 7 := by
    have h_temp : 14 * z = 98 := by
      rw [← sub_eq_zero] at h₁
      ring_nf at h₁
      have h_eq : 98 = z * 14 := by
        simpa [sub_eq_zero] using h₁
      rw [h_eq]
      ring
    
    have h_const : (14 : ℂ) * 7 = 98 := by norm_num
    apply mul_left_cancel₀ (show (14 : ℂ) ≠ 0 by norm_num)
    rw [h_temp, h_const]
  
  have h_f_val : f = -10 := by
    rw [h_f, h_z]
    norm_num
  
  exact ⟨h_f_val, h_z⟩
