import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3*z := by
    rw [← sub_eq_zero] at h₀
    ring_nf at h₀
    rw [← sub_eq_zero]
    ring_nf
    exact h₀
  
  rw [h₂] at h₁
  ring_nf at h₁
  have h₃ : z = 7 := by
    have h₄ : (14 : ℂ) * z = 98 := by
      rw [← sub_eq_zero] at h₁
      ring_nf at h₁
      rw [sub_eq_zero] at h₁
      rw [eq_comm] at h₁
      rw [mul_comm] at h₁
      exact h₁
    
    have h₆ : 14 * z = 14 * 7 := by
      rw [h₄]
      norm_num
    exact mul_left_cancel₀ (by norm_num) h₆
  
  have h₅ : f = -10 := by
    rw [h₂, h₃]
    norm_num
  
  exact ⟨h₅, h₃⟩
