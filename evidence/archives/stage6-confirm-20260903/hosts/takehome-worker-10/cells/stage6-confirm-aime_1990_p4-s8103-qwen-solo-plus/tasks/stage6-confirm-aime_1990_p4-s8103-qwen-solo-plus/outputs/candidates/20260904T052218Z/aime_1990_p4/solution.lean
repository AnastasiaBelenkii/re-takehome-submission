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
  
  field_simp [h₁', h₂', h₃'] at h₄'
  ring_nf at h₄'
  
  have h_y : y = 39 := by
    linarith [h₄']
  
  rw [hy] at h_y
  have h_x_sq : x^2 - 10 * x - 39 = 0 := by linarith
  have h_factor : (x - 13) * (x + 3) = 0 := by
    calc
      (x - 13) * (x + 3) = x^2 - 10 * x - 39 := by ring
      _ = 0 := by rw [h_x_sq]
  have h_cases : x = 13 ∨ x = -3 := by
    have : x - 13 = 0 ∨ x + 3 = 0 := by exact mul_eq_zero.mp h_factor
    cases this with
    | inl h => exact Or.inl (by linarith)
    | inr h => exact Or.inr (by linarith)
  cases h_cases with
  | inl h => exact h
  | inr h =>
    have h_neg : x < 0 := by linarith
    linarith [h₀]
