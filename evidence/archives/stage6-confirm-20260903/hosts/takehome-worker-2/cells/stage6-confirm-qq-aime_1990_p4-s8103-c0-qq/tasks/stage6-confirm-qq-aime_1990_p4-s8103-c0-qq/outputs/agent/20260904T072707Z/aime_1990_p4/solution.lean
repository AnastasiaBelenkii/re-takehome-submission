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
  set A := x^2 - 10 * x - 29
  set B := x^2 - 10 * x - 45
  set C := x^2 - 10 * x - 69
  
  have h₄' : 1 / A + 1 / B - 2 / C = 0 := by simpa [A, B, C] using h₄
  
  have h_prod_ne_zero : A * B * C ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero _ _
      · exact h₁
      · exact h₂
    · exact h₃
  
  have h_num : B * C + A * C - 2 * A * B = 0 := by
    have h_eq : (1 / A + 1 / B - 2 / C) * (A * B * C) = 0 := by
      rw [h₄']
      rw [zero_mul]
    
    calc
      B * C + A * C - 2 * A * B = (1 / A + 1 / B - 2 / C) * (A * B * C) := by
        field_simp [h₁, h₂, h₃]
        <;> ring
      _ = 0 := by rw [h_eq]
  
  have h_poly : (x^2 - 10 * x - 45) * (x^2 - 10 * x - 69) + (x^2 - 10 * x - 29) * (x^2 - 10 * x - 69) - 2 * (x^2 - 10 * x - 29) * (x^2 - 10 * x - 45) = 0 := by
    simp [A, B, C] at h_num
    exact h_num
  
  have h_expanded : 2 * (x^2 - 10 * x)^2 - 212 * (x^2 - 10 * x) + 5106 = 2 * (x^2 - 10 * x)^2 - 148 * (x^2 - 10 * x) + 2610 := by
    ring_nf at h_poly
    linarith
  
  have h_linear : -212 * (x^2 - 10 * x) + 5106 = -148 * (x^2 - 10 * x) + 2610 := by
    linarith
  
  have h_val : 64 * (x^2 - 10 * x) = 2496 := by
    linarith
  
  have h_u : x^2 - 10 * x = 39 := by
    apply mul_left_cancel₀ (show (64 : ℝ) ≠ 0 by norm_num)
    rw [h_val]
    norm_num
  
  have h_quad : x^2 - 10 * x - 39 = 0 := by
    linarith
  
  have h_factored : (x - 13) * (x + 3) = 0 := by
    calc
      (x - 13) * (x + 3) = x^2 - 10 * x - 39 := by ring
      _ = 0 := by rw [h_quad]
  
  have h_roots : x = 13 ∨ x = -3 := by
    have h_cases : x - 13 = 0 ∨ x + 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h_factored
    cases h_cases with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  
  cases h_roots with
  | inl h =>
    exact h
  | inr h =>
    exfalso
    linarith
