import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3 * z := by
    have := congr_arg (fun x => x - 3 * z) h₀
    ring_nf at this
    rw [mul_comm] at this
    exact this
  
  have h₃ : z = 7 := by
    rw [h₂] at h₁
    ring_nf at h₁
    -- Now h₁ is: 30 - 14 * z = -68
    -- We want to show 98 - 14 * z = 0
    have h₄ : 98 - 14 * z = 0 := by
      rw [← sub_eq_zero] at h₁
      ring_nf at h₁
      rw [mul_comm] at h₁
      exact h₁
    
    have h₅ : 14 * z = 98 := by
      rw [sub_eq_zero] at h₄
      rw [eq_comm] at h₄
      exact h₄
    
    have h₆ : z = 7 := by
      apply mul_left_cancel₀ (show (14 : ℂ) ≠ 0 by norm_num)
      rw [h₅]
      norm_num
    exact h₆
  
  have h₄ : f = -10 := by
    rw [h₂, h₃]
    norm_num
  
  exact ⟨h₄, h₃⟩
