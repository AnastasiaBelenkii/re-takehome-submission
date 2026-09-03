import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  have h1 : 7 ^ 4 % 100 = 1 := by norm_num
  have h2 : 2026 = 4 * 506 + 2 := by norm_num
  calc
    7 ^ 2026 % 100 = 7 ^ (4 * 506 + 2) % 100 := by rw [h2]
    _ = (7 ^ 4) ^ 506 * 7 ^ 2 % 100 := by
      rw [pow_add, pow_mul]
    _ = ((7 ^ 4) ^ 506 % 100) * (7 ^ 2 % 100) % 100 := by
      rw [Nat.mul_mod]
    _ = ((7 ^ 4) % 100) ^ 506 % 100 * (7 ^ 2 % 100) % 100 := by
      rw [Nat.pow_mod]
    _ = 1 ^ 506 % 100 * (7 ^ 2 % 100) % 100 := by
      rw [h1]
    _ = 1 * 49 % 100 := by norm_num
    _ = 49 := by norm_num
