import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  rw [show 7 ^ 2026 = 7 ^ (20 * 101 + 6) by norm_num]
  rw [pow_add, pow_mul]
  norm_num [pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
