import Mathlib

/-- What is the value of `x` if `x = (2009 ^ 2 - 2009) / 2009`? Show that it is `2008`. -/
theorem p02_frac_cancel (x : ℝ) (h : x = (2009 ^ 2 - 2009) / 2009) : x = 2008 := by
  -- First compute the fraction explicitly.
  have hcalc : (2009 ^ 2 - 2009) / (2009 : ℝ) = 2008 := by
    -- Clear the denominator and finish by ring reasoning.
    field_simp
    ring
  -- Replace the left‑hand side using the hypothesis `h`.
  simpa [h] using hcalc
