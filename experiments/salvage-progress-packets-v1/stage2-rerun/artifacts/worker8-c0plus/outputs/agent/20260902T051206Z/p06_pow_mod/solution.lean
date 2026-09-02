import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := first | omega | norm_num | nlinarith | linarith | ring | aesop | simp_all

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  first | omega | norm_num | nlinarith | linarith | ring | aesop | simp_all
