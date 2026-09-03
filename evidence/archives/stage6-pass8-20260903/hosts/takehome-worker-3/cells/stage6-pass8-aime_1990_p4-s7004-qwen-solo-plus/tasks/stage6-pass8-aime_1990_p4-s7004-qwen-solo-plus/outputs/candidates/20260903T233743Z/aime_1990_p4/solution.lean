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
  -- Normalize expressions to ensure field_simp can match denominators
  ring_nf at h₁ h₂ h₃ h₄
  
  -- Clear denominators and simplify the equation
  field_simp [h₁, h₂, h₃] at h₄
  ring_nf at h₄
  -- h₄ is now -64 * x ^ 2 + 640 * x + 2496 = 0
  
  -- Solve for x^2 - 10x
  have h_y : x^2 - 10 * x = 39 := by
    have h_div : -64 * (x^2 - 10 * x) + 2496 = 0 := by
      linarith
    have h_final : x^2 - 10 * x = 39 := by
      apply mul_left_cancel₀ (show (-64 : ℝ) ≠ 0 by norm_num)
      linarith
    exact h_final
  
  -- Solve quadratic x^2 - 10x - 39 = 0
  have h_root : x = 13 ∨ x = -3 := by
    have h₉ : x^2 - 10 * x - 39 = 0 := by linarith
    have h₁₀ : (x - 13) * (x + 3) = 0 := by
      ring_nf at h₉ ⊢
      linarith
    have h₁₁ : x - 13 = 0 ∨ x + 3 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h₁₀
    cases h₁₁ with
    | inl h₁₁ =>
      left
      linarith
    | inr h₁₁ =>
      right
      linarith
  
  -- Eliminate negative root
  cases h_root with
  | inl h_root =>
    exact h_root
  | inr h_root =>
    exfalso
    linarith
