import Mathlib

set_option exponentiation.threshold 5000

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  have h : 7 ^ 2026 % 100 = 49 := by
    norm_num
  simpa [p06_answer] using h
