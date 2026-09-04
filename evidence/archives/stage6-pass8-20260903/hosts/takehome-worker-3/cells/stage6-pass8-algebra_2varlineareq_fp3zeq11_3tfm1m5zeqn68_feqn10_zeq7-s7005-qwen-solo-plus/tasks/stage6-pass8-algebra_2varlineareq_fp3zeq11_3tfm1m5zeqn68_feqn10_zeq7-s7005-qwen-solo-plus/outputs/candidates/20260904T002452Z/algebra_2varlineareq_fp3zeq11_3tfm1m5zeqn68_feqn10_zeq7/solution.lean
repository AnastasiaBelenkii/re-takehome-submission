import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3*z := by
    rw [eq_sub_iff_add_eq]
    exact h₀
  
  rw [h₂] at h₁
  ring_nf at h₁
  have h₃ : 14 * z = 98 := by
    rw [← sub_eq_zero] at h₁
    ring_nf at h₁
    rw [sub_eq_zero] at h₁
    rw [eq_comm]
    rw [mul_comm] at h₁
    exact h₁
  
  have h₄ : z = 7 := by
    apply mul_left_cancel₀ (show (14 : ℂ) ≠ 0 by norm_num)
    rw [h₃]
    norm_num
  
  rw [h₄] at h₂
  ring_nf at h₂
  norm_num at h₂
  have h₅ : f = -10 := by
    exact h₂
  
  exact ⟨h₅, h₄⟩
