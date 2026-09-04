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
  have h_y_ne_29 : y - 29 ≠ 0 := by rw [hy]; exact h₁
  have h_y_ne_45 : y - 45 ≠ 0 := by rw [hy]; exact h₂
  have h_y_ne_69 : y - 69 ≠ 0 := by rw [hy]; exact h₃
  
  have h_eq : 1 / (y - 29) + 1 / (y - 45) = 2 / (y - 69) := by
    have h_rhs : 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69) = 0 := by
      rw [hy] at h₄
      exact h₄
    linarith
  
  have h_y_val : y = 39 := by
    have h_poly : (y - 45) * (y - 69) + (y - 29) * (y - 69) = 2 * (y - 29) * (y - 45) := by
      field_simp [h_y_ne_29, h_y_ne_45, h_y_ne_69] at h_eq
      ring_nf at h_eq ⊢
      linarith
    
    have h_linear : 32 * y = 1248 := by
      have h_diff : (y - 45) * (y - 69) + (y - 29) * (y - 69) - 2 * (y - 29) * (y - 45) = 0 := by linarith
      ring_nf at h_diff
      linarith
    
    linarith
  
  have h_x_sq : x^2 - 10 * x - 39 = 0 := by
    rw [hy] at h_y_val
    linarith
  
  have h_x_roots : x = 13 ∨ x = -3 := by
    have h_factored : (x - 13) * (x + 3) = 0 := by
      ring_nf at h_x_sq ⊢
      linarith
    have h_cases : x - 13 = 0 ∨ x + 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h_factored
    cases h_cases with
    | inl h =>
      have h_sol : x = 13 := by linarith
      exact Or.inl h_sol
    | inr h =>
      have h_sol : x = -3 := by linarith
      exact Or.inr h_sol
  
  cases h_x_roots with
  | inl h =>
    exact h
  | inr h =>
    have h_pos : 0 < x := h₀
    linarith
