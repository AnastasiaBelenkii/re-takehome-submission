import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  -- Step 1: Start with the fact that squares are always non-negative
  -- For any real number x, we have x^2 ≥ 0
  -- In particular, (a - b)^2 ≥ 0
  
  -- Step 2: Expand (a - b)^2 = a^2 - 2*a*b + b^2
  -- Since (a - b)^2 ≥ 0, we get a^2 - 2*a*b + b^2 ≥ 0
  
  -- Step 3: Rearrange the inequality to get a^2 + b^2 ≥ 2*a*b
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  -- Using the fact that (a - b)^2 ≥ 0 and expanding it
  have h2 : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := by
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      _ ≥ 0 := h
  -- Adding 2*a*b to both sides gives us the desired result
  linarith
