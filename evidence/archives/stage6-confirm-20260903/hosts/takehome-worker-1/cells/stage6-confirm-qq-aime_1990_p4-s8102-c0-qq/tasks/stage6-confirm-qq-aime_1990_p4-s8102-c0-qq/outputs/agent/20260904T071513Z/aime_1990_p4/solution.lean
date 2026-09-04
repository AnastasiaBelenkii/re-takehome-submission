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
  
  have h₁' : y - 29 ≠ 0 := by simpa [hy] using h₁
  have h₂' : y - 45 ≠ 0 := by simpa [hy] using h₂
  have h₃' : y - 69 ≠ 0 := by simpa [hy] using h₃
  have h₄' : 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69) = 0 := by
    simpa [hy] using h₄
  
  field_simp [h₁', h₂', h₃'] at h₄'
  ring_nf at h₄'
  
  have h_y : y = 39 := by
    linarith
  
  have h_x_quad : x^2 - 10 * x - 39 = 0 := by
    rw [← hy]
    linarith
  
  have h_factor : (x - 13) * (x + 3) = 0 := by
    ring_nf at h_x_quad ⊢
    exact h_x_quad
  
  have h_roots : x = 13 ∨ x = -3 := by
    have h_root_eq : x - 13 = 0 ∨ x + 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h_factor
    cases h_root_eq with
    | inl h =>
      have h_eq : x = 13 := by linarith
      exact Or.inl h_eq
    | inr h =>
      have h_eq : x = -3 := by linarith
      exact Or.inr h_eq
  
  cases h_roots with
  | inl h => exact h
  | inr h =>
    have h_contra : False := by linarith
    contradiction
