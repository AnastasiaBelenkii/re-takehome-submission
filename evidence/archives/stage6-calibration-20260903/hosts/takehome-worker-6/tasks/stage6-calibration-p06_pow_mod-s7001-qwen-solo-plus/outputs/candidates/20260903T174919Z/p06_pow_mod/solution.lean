import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  -- First show that 7^4 ≡ 1 (mod 100)
  have h1 : 7 ^ 4 % 100 = 1 := by norm_num
  -- Reduce the exponent: 2026 = 4 * 506 + 2
  have h2 : 7 ^ 2026 % 100 = 7 ^ 2 % 100 := by
    rw [show 2026 = 4 * 506 + 2 by norm_num]
    rw [pow_add, pow_mul]
    simp [h1, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]
  -- Compute 7^2 = 49
  rw [h2]
  norm_num
