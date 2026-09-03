import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  have h₁ : a * b = (1 - (a - b)^2) / 2 := by
    have h₁₁ : (a - b)^2 = a^2 - 2*a*b + b^2 := by ring
    rw [h₁₁] at *
    have h₁₂ : a^2 + b^2 = 1 := h₀
    linarith
  
  rw [h₁]
  -- Rewrite (a - b)^2 as |a - b|^2 to allow nlinarith to relate them
  have h₂ : (a - b)^2 = |a - b|^2 := by rw [← sq_abs]
  rw [h₂]
  -- Now the goal is (1 - |a - b|^2) / 2 + |a - b| ≤ 1
  -- This is equivalent to (|a - b| - 1)^2 ≥ 0
  nlinarith [sq_nonneg (|a - b| - 1)]
