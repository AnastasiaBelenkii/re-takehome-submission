import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^2 - 10 * x - 29 ≠ 0)
  (h₂ : x^2 - 10 * x - 45 ≠ 0)
  (h₃ : x^2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
  x = 13 := by
  set y := x^2 - 10 * x with hy
  
  have h₁' : y - 29 ≠ 0 := by rw [hy]; exact h₁
  have h₂' : y - 45 ≠ 0 := by rw [hy]; exact h₂
  have h₃' : y - 69 ≠ 0 := by rw [hy]; exact h₃
  
  have h₄' : 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69) = 0 := by
    rw [hy] at h₄
    exact h₄
  
  have h_y_val : y = 39 := by
    have h₅₁ : 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69) = 0 := h₄'
    field_simp [h₁', h₂', h₃'] at h₅₁
    ring_nf at h₅₁
    linarith
  
  have h₇ : x^2 - 10 * x = 39 := by
    rw [hy] at h_y_val
    exact h_y_val
  
  have h₈ : x^2 - 10 * x - 39 = 0 := by linarith
  
  have h₉ : (x - 13) * (x + 3) = 0 := by
    ring_nf at h₈ ⊢
    linarith
  
  have h₁₀ : x - 13 = 0 ∨ x + 3 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h₉
  
  cases h₁₀ with
  | inl h₁₀ =>
    have h₁₁ : x = 13 := by linarith
    exact h₁₁
  | inr h₁₀ =>
    have h₁₁ : x = -3 := by linarith
    have h₁₂ : x > 0 := h₀
    linarith
