import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · -- Forward direction: if 7 divides 2^n - 1, then 3 divides n
    intro h
    have h_mod : (2 ^ n) % 7 = 1 := by
      have : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
      have : 2 ^ n ≥ 1 := Nat.one_le_pow n 2 (by norm_num)
      have : (2 ^ n) % 7 = 1 := by
        omega
      exact this
    -- Use the fact that 2^n mod 7 cycles with period 3
    have : n % 3 = 0 := by
      have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases this with (h1 | h1 | h1)
      · exact h1
      · -- Case n % 3 = 1: 2^n ≡ 2 (mod 7) ≠ 1
        exfalso
        have : (2 ^ n) % 7 = 2 := by
          rw [← Nat.mod_add_div n 3]
          simp [h1, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod]
          <;> norm_num
        omega
      · -- Case n % 3 = 2: 2^n ≡ 4 (mod 7) ≠ 1
        exfalso
        have : (2 ^ n) % 7 = 4 := by
          rw [← Nat.mod_add_div n 3]
          simp [h1, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod]
          <;> norm_num
        omega
    omega
  · -- Backward direction: if 3 divides n, then 7 divides 2^n - 1
    intro h
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul]
    -- We need to show 7 ∣ 8^k - 1
    -- It suffices to show 8^k ≡ 1 [MOD 7]
    have h_mod : (8 : ℕ) ^ k % 7 = 1 := by
      have : (8 : ℕ) ≡ 1 [MOD 7] := by norm_num
      have : (8 : ℕ) ^ k ≡ 1 [MOD 7] := by
        simpa using (Nat.ModEq.pow k this)
      simpa [Nat.ModEq] using this
    have : 7 ∣ 8 ^ k - 1 := by
      have : (8 ^ k - 1) % 7 = 0 := by
        have : 8 ^ k % 7 = 1 := h_mod
        have : 8 ^ k ≥ 1 := Nat.one_le_pow k 8 (by norm_num)
        omega
      exact Nat.dvd_of_mod_eq_zero this
    exact this

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  -- Show that 2^n + 1 is never 0 mod 7 for any n
  have : (2 ^ n) % 7 = 1 ∨ (2 ^ n) % 7 = 2 ∨ (2 ^ n) % 7 = 4 := by
    have : ∀ m : ℕ, (2 ^ m) % 7 = 1 ∨ (2 ^ m) % 7 = 2 ∨ (2 ^ m) % 7 = 4 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rcases ih with (h1 | h1 | h1)
        · simp [pow_succ, Nat.mul_mod, h1] <;> norm_num
        · simp [pow_succ, Nat.mul_mod, h1] <;> norm_num
        · simp [pow_succ, Nat.mul_mod, h1] <;> norm_num
    exact this n
  rcases this with (h1 | h1 | h1)
  · -- Case 2^n ≡ 1 (mod 7): 2^n + 1 ≡ 2 (mod 7) ≠ 0
    omega
  · -- Case 2^n ≡ 2 (mod 7): 2^n + 1 ≡ 3 (mod 7) ≠ 0
    omega
  · -- Case 2^n ≡ 4 (mod 7): 2^n + 1 ≡ 5 (mod 7) ≠ 0
    omega
