import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  have h_div : 2026 = 4 * 506 + 2 := by norm_num
  rw [h_div]
  rw [pow_add, pow_mul, pow_two]
  norm_num [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
