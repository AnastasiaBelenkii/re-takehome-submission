import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  -- First show that 7^4 ≡ 1 (mod 100)
  have h1 : 7 ^ 4 % 100 = 1 := by norm_num
  -- Write 2026 = 4 * 506 + 2
  have h2 : 2026 = 4 * 506 + 2 := by norm_num
  -- Use the fact that 7^4 ≡ 1 to reduce the exponent
  rw [h2]
  simp only [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
  -- Now compute 7^2 % 100 = 49
  norm_num [h1]
