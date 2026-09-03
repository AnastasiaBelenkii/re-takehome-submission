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
  have h₃ : x - p ≥ 0 := by linarith
  have h₄ : abs (x - p) = x - p := by rw [abs_of_nonneg h₃]
  
  have h₅ : x - 15 ≤ 0 := by linarith
  have h₆ : abs (x - 15) = 15 - x := by
    rw [abs_of_nonpos h₅]
    ring
  
  have h₇ : x - p - 15 < 0 := by linarith
  have h₈ : abs (x - p - 15) = -(x - p - 15) := by rw [abs_of_neg h₇]
  have h₉ : abs (x - p - 15) = 15 + p - x := by
    rw [h₈]
    ring
  
  calc
    f x = abs (x - p) + abs (x - 15) + abs (x - p - 15) := by rw [h₂]
    _ = (x - p) + (15 - x) + (15 + p - x) := by rw [h₄, h₆, h₉]
    _ = 30 - x := by ring
    _ ≥ 15 := by linarith
