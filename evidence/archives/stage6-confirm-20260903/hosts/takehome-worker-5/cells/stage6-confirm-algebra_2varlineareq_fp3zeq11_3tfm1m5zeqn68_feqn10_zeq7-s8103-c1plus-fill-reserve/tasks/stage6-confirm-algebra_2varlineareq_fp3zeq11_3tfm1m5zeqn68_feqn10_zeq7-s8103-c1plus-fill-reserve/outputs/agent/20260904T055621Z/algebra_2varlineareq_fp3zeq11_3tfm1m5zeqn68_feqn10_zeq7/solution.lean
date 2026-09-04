import Mathlib

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3*z := by
    have := congr_arg (fun x => x - 3*z) h₀
    simp at this
    exact this
  
  have h₃ : z = 7 := by
    rw [h₂] at h₁
    ring_nf at h₁
    -- h₁ is now 30 - 14*z = -68
    
    have h₃' : 14 * z = 98 := by
      rw [← sub_eq_zero]
      -- Goal is 14 * z - 98 = 0
      rw [← neg_eq_zero]
      -- Goal is -(14 * z - 98) = 0
      ring_nf
      -- Goal is 98 - 14 * z = 0
      
      rw [← sub_eq_zero] at h₁
      -- h₁ is now 30 - 14 * z - (-68) = 0
      ring_nf at h₁
      -- h₁ is now 98 - 14 * z = 0
      
      exact h₁
    
    have h₃'' : z = 7 := by
      have h₃''' : (14 : ℂ) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h₃'''
      rw [h₃']
      norm_num
    exact h₃''

  have h₄ : f = -10 := by
    rw [h₂, h₃]
    norm_num
  
  exact ⟨h₄, h₃⟩
