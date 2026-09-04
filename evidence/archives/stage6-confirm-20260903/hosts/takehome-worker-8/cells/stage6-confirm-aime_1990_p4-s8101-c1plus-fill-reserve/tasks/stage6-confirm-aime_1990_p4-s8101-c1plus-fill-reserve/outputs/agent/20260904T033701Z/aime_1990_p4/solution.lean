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
  set y := x^2 - 10 * x
  have hy₁ : y - 29 ≠ 0 := by simpa [y] using h₁
  have hy₂ : y - 45 ≠ 0 := by simpa [y] using h₂
  have hy₃ : y - 69 ≠ 0 := by simpa [y] using h₃
  have h_y_eq : 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69) = 0 := by
    simpa [y] using h₄
  
  have h_y_val : y = 39 := by
    field_simp [hy₁, hy₂, hy₃] at h_y_eq
    ring_nf at h_y_eq
    linarith
  
  have h_x_quad : x^2 - 10 * x - 39 = 0 := by
    have h₉ : x^2 - 10 * x = 39 := by
      simpa [y] using h_y_val
    linarith
  
  have h_x_factored : (x - 13) * (x + 3) = 0 := by
    have h₁₀ : x^2 - 10 * x - 39 = 0 := h_x_quad
    have h₁₁ : (x - 13) * (x + 3) = x^2 - 10 * x - 39 := by ring
    rw [h₁₁]
    exact h₁₀
  
  have h_x_sol : x = 13 ∨ x = -3 := by
    have h₁₂ : x - 13 = 0 ∨ x + 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h_x_factored
    cases h₁₂ with
    | inl h => exact Or.inl (by linarith)
    | inr h => exact Or.inr (by linarith)
  
  cases h_x_sol with
  | inl h => exact h
  | inr h =>
    have h₁₃ : x = -3 := h
    have h₁₄ : 0 < x := h₀
    linarith
