import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + (a - b) ≤ 1 := by
  -- Use the identity (a-b)^2 = a^2 - 2ab + b^2 = 1 - 2ab
  -- This gives us ab = (1 - (a-b)^2)/2
  have h₁ : a * b = (1 - (a - b)^2) / 2 := by
    have h₂ : (a - b)^2 = a^2 - 2*a*b + b^2 := by ring
    rw [h₂] at *
    have h₃ : a^2 + b^2 = 1 := h₀
    nlinarith
  
  -- Substitute ab in the target inequality
  rw [h₁]
  
  -- Let x = a - b, then we need to show (1 - x^2)/2 + x ≤ 1
  -- This simplifies to -(x-1)^2 ≤ 0, which is always true
  nlinarith [sq_nonneg (a - b - 1)]
