import Mathlib

/-- What is the value of `x` if `x = (2009 ^ 2 - 2009) / 2009`? Show that it is `2008`. -/
theorem p02_frac_cancel (x : ℝ) (h : x = (2009 ^ 2 - 2009) / 2009) : x = 2008 := by
  rw [h]
  -- Substitute the given expression for x
  have h₁ : (2009 : ℝ) ≠ 0 := by norm_num
  -- Establish that 2009 is non-zero for division
  field_simp [h₁]
  -- Cancel the common factor of 2009 in numerator and denominator
  ring_nf
  all_goals rfl
