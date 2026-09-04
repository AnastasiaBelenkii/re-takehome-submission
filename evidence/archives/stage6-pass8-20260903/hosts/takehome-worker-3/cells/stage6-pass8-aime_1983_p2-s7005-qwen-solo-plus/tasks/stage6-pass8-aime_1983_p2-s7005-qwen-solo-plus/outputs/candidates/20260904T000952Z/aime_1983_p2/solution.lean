import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p2
  (x p : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < p ∧ p < 15)
  (h₁ : p ≤ x ∧ x ≤ 15)
  (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
  15 ≤ f x := by
  have h₃ : x - p ≥ 0 := by linarith [h₁.1]
  have h₄ : x - 15 ≤ 0 := by linarith [h₁.2]
  have h₅ : x - p - 15 < 0 := by linarith [h₀.1, h₁.2]
  
  have h₆ : abs (x - p) = x - p := by rw [abs_of_nonneg h₃]
  have h₇ : abs (x - 15) = 15 - x := by rw [abs_of_nonpos h₄]; ring_nf
  have h₈ : abs (x - p - 15) = 15 + p - x := by rw [abs_of_neg h₅]; ring_nf
  
  rw [h₂, h₆, h₇, h₈]
  ring_nf
  linarith [h₁.2]
