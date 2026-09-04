import Mathlib

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z : ℂ)
  (h₀ : f + 3 * z = 11)
  (h₁ : 3 * (f - 1) - 5 * z = -68) :
  f = -10 ∧ z = 7 := by
  have h₂ : f = 11 - 3 * z := by
    rw [← sub_eq_zero] at h₀
    rw [← sub_eq_zero]
    ring_nf at h₀ ⊢
    exact h₀
  
  rw [h₂] at h₁
  have h₃ : 3 * ((11 - 3 * z) - 1) - 5 * z = -68 := h₁
  
  have h₄ : 30 - 14 * z = -68 := by
    ring_nf at h₃
    rw [← mul_comm] at h₃
    exact h₃
  
  have h₅ : 14 * z = 98 := by
    rw [← sub_eq_zero] at h₄
    ring_nf at h₄
    rw [sub_eq_zero] at h₄
    rw [eq_comm] at h₄
    rw [← mul_comm] at h₄
    exact h₄
  
  have h₆ : z = 7 := by
    apply mul_left_cancel₀ (show (14 : ℂ) ≠ 0 by norm_num)
    rw [h₅]
    norm_num
  
  have h₇ : f = -10 := by
    rw [h₂, h₆]
    norm_num
  
  exact ⟨h₇, h₆⟩
