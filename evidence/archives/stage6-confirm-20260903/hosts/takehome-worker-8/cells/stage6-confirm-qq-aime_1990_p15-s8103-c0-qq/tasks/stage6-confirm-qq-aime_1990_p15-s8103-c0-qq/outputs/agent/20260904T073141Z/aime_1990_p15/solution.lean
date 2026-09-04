import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x^2 + b * y^2 = 7)
  (h₂ : a * x^3 + b * y^3 = 16)
  (h₃ : a * x^4 + b * y^4 = 42) :
  a * x^5 + b * y^5 = 20 := by
  have h_rec3 : a * x^5 + b * y^5 = (x + y) * (a * x^4 + b * y^4) - (x * y) * (a * x^3 + b * y^3) := by ring
  have h_rec2 : a * x^4 + b * y^4 = (x + y) * (a * x^3 + b * y^3) - (x * y) * (a * x^2 + b * y^2) := by ring
  have h_rec1 : a * x^3 + b * y^3 = (x + y) * (a * x^2 + b * y^2) - (x * y) * (a * x + b * y) := by ring
  
  have h_eq1 : (x + y) * 7 - x * y * 3 = 16 := by
    rw [h_rec1] at h₂
    rw [h₁, h₀] at h₂
    exact h₂
  
  have h_eq2 : (x + y) * 16 - x * y * 7 = 42 := by
    rw [h_rec2] at h₃
    rw [h₂, h₁] at h₃
    exact h₃
  
  have h_sum : x + y = -14 := by
    have hA : (x + y) * 7 - x * y * 3 = 16 := h_eq1
    have hB : (x + y) * 16 - x * y * 7 = 42 := h_eq2
    have hC : 7 * ((x + y) * 7 - x * y * 3) - 3 * ((x + y) * 16 - x * y * 7) = 7 * 16 - 3 * 42 := by
      rw [hA, hB]
    ring_nf at hC
    linarith
  
  have h_prod : x * y = -38 := by
    have hA : (x + y) * 7 - x * y * 3 = 16 := h_eq1
    rw [h_sum] at hA
    ring_nf at hA
    linarith
  
  calc
    a * x^5 + b * y^5 = (x + y) * (a * x^4 + b * y^4) - (x * y) * (a * x^3 + b * y^3) := by rw [h_rec3]
    _ = (x + y) * 42 - (x * y) * 16 := by
      rw [h₃, h₂]
      <;> ring
    _ = (-14) * 42 - (-38) * 16 := by
      rw [h_sum, h_prod]
    _ = 20 := by norm_num
