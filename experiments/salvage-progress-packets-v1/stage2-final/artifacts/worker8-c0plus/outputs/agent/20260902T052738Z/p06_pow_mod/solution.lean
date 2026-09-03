import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  -- We evaluate the huge power modulo 100 using `norm_num`.
  -- The tactic efficiently reduces the exponent and carries out the modular arithmetic.
  norm_num
