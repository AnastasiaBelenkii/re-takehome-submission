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
  let y := x^2 - 10 * x
  have h₁' : y - 29 ≠ 0 := by simpa [y] using h₁
  have h₂' : y - 45 ≠ 0 := by simpa [y] using h₂
  have h₃' : y - 69 ≠ 0 := by simpa [y] using h₃
  
  have h₄' : 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69) = 0 := by
    simpa [y] using h₄
  
  have h_y : y = 39 := by
    field_simp [h₁', h₂', h₃'] at h₄'
    ring_nf at h₄'
    linarith
  
  have h_x_eq : x^2 - 10 * x = 39 := by
    simpa [y] using h_y
  
  have h_quadratic : x^2 - 10 * x - 39 = 0 := by linarith
  
  have h_factorized : (x - 13) * (x + 3) = 0 := by
    rw [show (x - 13) * (x + 3) = x^2 - 10 * x - 39 by ring]
    exact h_quadratic
  
  have h_roots : x - 13 = 0 ∨ x + 3 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h_factorized
  
  cases h_roots with
  | inl h =>
    have h_final : x = 13 := by linarith
    exact h_final
  | inr h =>
    have h_neg : x = -3 := by linarith
    have h_pos : 0 < x := h₀
    linarith
