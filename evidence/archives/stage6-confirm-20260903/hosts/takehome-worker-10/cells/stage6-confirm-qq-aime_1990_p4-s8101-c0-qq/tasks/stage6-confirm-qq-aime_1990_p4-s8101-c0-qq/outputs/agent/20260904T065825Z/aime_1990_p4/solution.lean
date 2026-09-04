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
  field_simp [h₁, h₂, h₃] at h₄
  ring_nf at h₄
  have h_y_eq_39 : y = 39 := by
    linarith [h₄]
  rw [h_y_eq_39] at hy
  have h_x_poly : x^2 - 10 * x - 39 = 0 := by
    linarith
  have h_x_roots : x = 13 ∨ x = -3 := by
    have h_prod : (x - 13) * (x + 3) = 0 := by
      calc
        (x - 13) * (x + 3) = x^2 - 10 * x - 39 := by ring
        _ = 0 := h_x_poly
    have h_cases : x - 13 = 0 ∨ x + 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h_prod
    cases h_cases with
    | inl h => exact Or.inl (by linarith)
    | inr h => exact Or.inr (by linarith)
  cases h_x_roots with
  | inl h => exact h
  | inr h => linarith [h₀]
