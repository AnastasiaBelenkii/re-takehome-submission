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
  -- From h₁, we have p ≤ x and x ≤ 15
  -- This means x - p ≥ 0, x - 15 ≤ 0, and x - p - 15 ≤ 0
  have h₃ : x - p ≥ 0 := by linarith
  have h₄ : x - 15 ≤ 0 := by linarith
  have h₅ : x - p - 15 ≤ 0 := by linarith
  -- Simplify the absolute values using these inequalities
  have h₆ : abs (x - p) = x - p := by rw [abs_of_nonneg h₃]
  have h₇ : abs (x - 15) = -(x - 15) := by rw [abs_of_nonpos h₄]
  have h₈ : abs (x - p - 15) = -(x - p - 15) := by rw [abs_of_nonpos h₅]
  -- Substitute back into f(x) and simplify
  have h₉ : f x = 30 - x := by
    rw [h₂, h₆, h₇, h₈]
    ring_nf
    <;> linarith
  -- Since x ≤ 15, we have 30 - x ≥ 15
  linarith
