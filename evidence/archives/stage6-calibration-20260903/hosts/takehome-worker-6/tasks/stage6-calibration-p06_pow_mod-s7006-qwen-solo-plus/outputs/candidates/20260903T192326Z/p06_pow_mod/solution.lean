import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  have h : 7 ^ 4 % 100 = 1 := by norm_num
  have h2 : 2026 = 4 * 506 + 2 := by norm_num
  rw [h2]
  rw [pow_add]
  rw [pow_mul]
  rw [Nat.mul_mod]
  rw [Nat.pow_mod]
  rw [h]
  norm_num
