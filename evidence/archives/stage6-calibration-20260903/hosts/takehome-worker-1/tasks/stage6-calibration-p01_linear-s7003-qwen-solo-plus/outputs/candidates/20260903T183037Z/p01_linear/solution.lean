import Mathlib

/-- If `3 * x + 7 = 22` for a real number `x`, then `x = 5`. -/
theorem p01_linear (x : ℝ) (h : 3 * x + 7 = 22) : x = 5 := by
  -- Subtract 7 from both sides: 3 * x = 15
  have h1 : 3 * x = 15 := by
    linarith
  
  -- Divide both sides by 3: x = 5
  have h2 : x = 5 := by
    linarith
  
  -- Conclude the proof
  exact h2
