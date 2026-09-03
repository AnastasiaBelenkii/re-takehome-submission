import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + (a - b) ≤ 1 := by
  -- Use the fact that (a - b)^2 >= 0 implies a^2 + b^2 >= 2ab
  have h₁ : a * b ≤ 1 / 2 := by
    nlinarith [sq_nonneg (a - b)]
  
  -- Consider the expression (a - 1/2)^2 + (b + 1/2)^2 >= 0
  -- This expands to a^2 - a + 1/4 + b^2 + b + 1/4 >= 0
  -- Using a^2 + b^2 = 1, we get 1 - a + b + 1/2 >= 0
  -- So a - b <= 3/2
  
  -- More directly, consider (a - b - 1)^2 >= 0
  -- This gives a^2 + b^2 - 2ab - 2a + 2b + 1 >= 0
  -- Using a^2 + b^2 = 1, we get 1 - 2ab - 2a + 2b + 1 >= 0
  -- So 2 - 2ab - 2a + 2b >= 0
  -- Dividing by 2: 1 - ab - a + b >= 0
  -- Rearranging: ab + a - b <= 1
  
  nlinarith [sq_nonneg (a - b - 1), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b + 1)]
