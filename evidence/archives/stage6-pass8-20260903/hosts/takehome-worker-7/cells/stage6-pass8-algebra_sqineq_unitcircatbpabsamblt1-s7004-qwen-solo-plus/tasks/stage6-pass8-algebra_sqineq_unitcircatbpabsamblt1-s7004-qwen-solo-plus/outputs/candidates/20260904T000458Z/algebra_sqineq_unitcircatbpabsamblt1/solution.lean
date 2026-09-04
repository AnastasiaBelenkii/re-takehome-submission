import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  -- Use the identity (a-b)^2 = a^2 - 2ab + b^2 to express ab in terms of (a-b)^2
  have h₁ : a * b = (1 - (a - b)^2) / 2 := by
    have h₂ : (a - b)^2 = a^2 - 2*a*b + b^2 := by ring
    rw [h₂] at *
    linarith
  
  -- Substitute ab into the inequality and simplify
  rw [h₁]
  
  -- Let x = |a - b| and show (1 - x^2)/2 + x ≤ 1
  have h₃ : (1 - (a - b)^2) / 2 + |a - b| ≤ 1 := by
    cases' le_total 0 (a - b) with h₄ h₄
    · -- Case: a - b ≥ 0, so |a - b| = a - b
      rw [abs_of_nonneg h₄]
      nlinarith [sq_nonneg (a - b - 1)]
    · -- Case: a - b < 0, so |a - b| = -(a - b) = b - a
      rw [abs_of_nonpos h₄]
      nlinarith [sq_nonneg (a - b + 1)]
  
  exact h₃
