import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  have h₁ : 2 * a * b = 1 - (a - b)^2 := by
    calc
      2 * a * b = 1 - (a^2 + b^2) + 2 * a * b := by
        rw [h₀]
        <;> ring
      _ = 1 - (a^2 - 2 * a * b + b^2) := by ring
      _ = 1 - (a - b)^2 := by ring
  
  have h₂ : (a - b)^2 = |a - b|^2 := by
    rw [← sq_abs]
  
  have h₃ : 2 * (a * b + |a - b|) ≤ 2 := by
    calc
      2 * (a * b + |a - b|) = 2 * a * b + 2 * |a - b| := by ring
      _ = (1 - (a - b)^2) + 2 * |a - b| := by rw [h₁]
      _ = 1 - |a - b|^2 + 2 * |a - b| := by rw [h₂]
      _ = 2 - (|a - b| - 1)^2 := by ring
      _ ≤ 2 := by
        have h₄ : 0 ≤ (|a - b| - 1)^2 := sq_nonneg _
        linarith
  
  linarith
