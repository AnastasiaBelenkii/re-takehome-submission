import Mathlib

abbrev p06_answer : ℕ := 49

theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by
  have h_period : 7 ^ 4 % 100 = 1 := by norm_num
  have h_exp : 2026 = 4 * 506 + 2 := by norm_num
  
  calc
    7 ^ 2026 % 100 
      = 7 ^ (4 * 506 + 2) % 100 := by rw [h_exp]
    _ = (7 ^ (4 * 506) * 7 ^ 2) % 100 := by rw [pow_add]
    _ = ((7 ^ 4) ^ 506 * 7 ^ 2) % 100 := by rw [pow_mul]
    _ = (((7 ^ 4) ^ 506 % 100) * (7 ^ 2 % 100)) % 100 := by
      -- Use Nat.mul_mod carefully
      -- To ensure (a * b) % n -> (a % n * b % n) % n
      -- With explicit parens, we can guide the parser.
      -- But rw [Nat.mul_mod] might not match if parens differ.
      -- Let's try to use simp with Nat.mul_mod.
      simp [Nat.mul_mod]
    _ = (1 * 49) % 100 := by
      have h_pow : ((7 ^ 4) ^ 506) % 100 = 1 := by
        rw [Nat.pow_mod]
        rw [h_period]
        norm_num
      have h_sq : 7 ^ 2 % 100 = 49 := by norm_num
      rw [h_pow, h_sq]
    _ = 49 := by norm_num
