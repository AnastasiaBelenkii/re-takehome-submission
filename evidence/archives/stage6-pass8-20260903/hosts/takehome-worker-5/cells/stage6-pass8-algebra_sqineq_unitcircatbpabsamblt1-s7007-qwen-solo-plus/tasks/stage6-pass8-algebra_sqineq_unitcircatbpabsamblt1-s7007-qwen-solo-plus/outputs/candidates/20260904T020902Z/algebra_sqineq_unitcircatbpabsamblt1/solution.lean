import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  -- Use the identity (a-b)^2 = a^2 - 2ab + b^2 = 1 - 2ab to express ab in terms of (a-b)^2
  have h₁ : a * b = (1 - (a - b)^2) / 2 := by
    have h₁' : (a - b)^2 = a^2 - 2*a*b + b^2 := by ring
    rw [h₁'] at *
    have h₂ : a^2 + b^2 = 1 := h₀
    linarith
  
  -- Substitute ab with (1 - (a-b)^2)/2 and let x = |a-b|
  -- We need to show (1 - x^2)/2 + x ≤ 1 for x ≥ 0
  have h₂ : a * b + |a - b| ≤ 1 := by
    have h₃ : a * b + |a - b| = (1 - (a - b)^2) / 2 + |a - b| := by
      rw [h₁]
      <;> ring
    rw [h₃]
    
    -- Let x = |a - b|, then (a-b)^2 = x^2
    have h₄ : (a - b)^2 = |a - b|^2 := by
      simp [sq_abs]
    rw [h₄]
    
    -- Show that (1 - x^2)/2 + x ≤ 1 is equivalent to -(x-1)^2 ≤ 0
    have h₅ : (1 - |a - b|^2) / 2 + |a - b| ≤ 1 := by
      nlinarith [sq_nonneg (|a - b| - 1)]
    
    exact h₅
  
  exact h₂
