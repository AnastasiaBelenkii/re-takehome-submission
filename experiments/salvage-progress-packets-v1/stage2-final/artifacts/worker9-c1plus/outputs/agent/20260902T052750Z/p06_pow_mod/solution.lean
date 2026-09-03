import Mathlib

/-- The last two digits of `7 ^ 2026`. Must be a numeric literal. -/
abbrev p06_answer : ℕ := 49

/-- Compute `7 ^ 2026 % 100`. -/
theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  -- First show that 7^4 ≡ 1 (mod 100) by direct computation
  have h1 : 7 ^ 4 % 100 = 1 := by norm_num
  -- Express 2026 as 4 * 506 + 2
  have h2 : 2026 = 4 * 506 + 2 := by norm_num
  -- Rewrite the exponent
  rw [h2]
  -- Expand using pow_add and pow_mul
  rw [pow_add, pow_mul]
  -- Simplify using the fact that 7^4 ≡ 1 (mod 100)
  rw [← Nat.mod_add_div (7 ^ 4) 100]
  simp [Nat.mul_mod, Nat.pow_mod, h1]
  -- Final computation gives 49
  <;> norm_num
