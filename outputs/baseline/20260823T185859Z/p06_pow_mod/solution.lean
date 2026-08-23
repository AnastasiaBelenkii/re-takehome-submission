import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  rw [show 2026 = 4 * 506 + 2 by norm_num]
  rw [pow_add, pow_mul]
  simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  <;> norm_num
  <;> rfl
