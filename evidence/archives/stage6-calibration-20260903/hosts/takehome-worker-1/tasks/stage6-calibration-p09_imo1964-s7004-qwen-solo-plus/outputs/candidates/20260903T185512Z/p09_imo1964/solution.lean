import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · -- Forward direction: if 7 divides 2^n - 1, then 3 divides n
    intro h
    have h₁ : 2 ^ n % 7 = 1 := by
      have h₂ : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
      have h₃ : 2 ^ n % 7 = 1 := by
        have h₄ : 2 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          omega
        omega
      exact h₃
    -- Use the fact that 2^n mod 7 cycles through 2, 4, 1 with period 3
    have h₂ : n % 3 = 0 := by
      have h₃ : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
          <;> norm_num
      have h₄ : ∀ k : ℕ, 2 ^ (3 * k + 1) % 7 = 2 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
          <;> norm_num
      have h₅ : ∀ k : ℕ, 2 ^ (3 * k + 2) % 7 = 4 := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
          <;> norm_num
      have h₆ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h₆ with (h₆ | h₆ | h₆)
      · exact h₆
      · exfalso
        have h₇ : 2 ^ n % 7 = 2 := by
          rw [← Nat.mod_add_div n 3]
          simp [h₆, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
          <;> norm_num
        omega
      · exfalso
        have h₇ : 2 ^ n % 7 = 4 := by
          rw [← Nat.mod_add_div n 3]
          simp [h₆, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
          <;> norm_num
        omega
    omega
  · -- Backward direction: if 3 divides n, then 7 divides 2^n - 1
    intro h
    obtain ⟨k, rfl⟩ := h
    have h₁ : 2 ^ (3 * k) % 7 = 1 := by
      induction k with
      | zero => simp
      | succ k ih =>
        simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
        <;> norm_num
    have h₂ : (2 ^ (3 * k) - 1) % 7 = 0 := by
      have h₃ : 2 ^ (3 * k) ≥ 1 := by
        apply Nat.one_le_pow
        omega
      omega
    exact Nat.dvd_of_mod_eq_zero h₂

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h₁ : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  have h₂ : 2 ^ n % 7 = 6 := by
    have h₃ : 2 ^ n ≥ 1 := by
      apply Nat.one_le_pow
      omega
    omega
  -- Check all possible values of 2^n mod 7
  have h₃ : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
      <;> norm_num
  have h₄ : ∀ k : ℕ, 2 ^ (3 * k + 1) % 7 = 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
      <;> norm_num
  have h₅ : ∀ k : ℕ, 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, ih]
      <;> norm_num
  have h₆ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h₆ with (h₆ | h₆ | h₆)
  · exfalso
    have h₇ : 2 ^ n % 7 = 1 := by
      rw [← Nat.mod_add_div n 3]
      simp [h₆, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
      <;> norm_num
    omega
  · exfalso
    have h₇ : 2 ^ n % 7 = 2 := by
      rw [← Nat.mod_add_div n 3]
      simp [h₆, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
      <;> norm_num
    omega
  · exfalso
    have h₇ : 2 ^ n % 7 = 4 := by
      rw [← Nat.mod_add_div n 3]
      simp [h₆, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
      <;> norm_num
    omega
