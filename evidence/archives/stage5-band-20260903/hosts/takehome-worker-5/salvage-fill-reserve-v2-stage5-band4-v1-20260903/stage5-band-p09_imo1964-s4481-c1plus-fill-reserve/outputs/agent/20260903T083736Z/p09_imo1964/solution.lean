import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  -- Use modular arithmetic to analyze powers of 2 mod 7
  -- Powers of 2 mod 7 cycle with period 3: 2, 4, 1, 2, 4, 1, ...
  have h : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ]
      simp [pow_add, pow_mul, Nat.pow_mod, ih, Nat.mul_mod]
      <;> norm_num
  have h2 : ∀ k : ℕ, 2 ^ (3 * k + 1) % 7 = 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Nat.add_assoc]
      simp [pow_add, pow_mul, Nat.pow_mod, ih, Nat.mul_mod]
      <;> norm_num
  have h3 : ∀ k : ℕ, 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Nat.add_assoc]
      simp [pow_add, pow_mul, Nat.pow_mod, ih, Nat.mul_mod]
      <;> norm_num
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1 then 3 ∣ n
    intro hdiv
    have hmod : 2 ^ n % 7 = 1 := by
      have h1 : 2 ^ n % 7 = (2 ^ n - 1 + 1) % 7 := by
        have h2 : 1 ≤ 2 ^ n := by
          apply Nat.one_le_pow
          omega
        omega
      rw [h1]
      have h3 : (2 ^ n - 1 + 1) % 7 = (2 ^ n - 1) % 7 + 1 % 7 := by
        omega
      rw [h3]
      have h4 : 7 ∣ 2 ^ n - 1 := hdiv
      have h5 : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h4
      omega
    -- Now show that n must be divisible by 3
    have hcase : n % 3 = 0 := by
      have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h1 with (h1 | h1 | h1)
      · exact h1
      · -- Case n ≡ 1 (mod 3)
        have h2 : ∃ k, n = 3 * k + 1 := by
          use n / 3
          omega
        rcases h2 with ⟨k, hk⟩
        rw [hk] at hmod
        have h3 := h2 k
        omega
      · -- Case n ≡ 2 (mod 3)
        have h2 : ∃ k, n = 3 * k + 2 := by
          use n / 3
          omega
        rcases h2 with ⟨k, hk⟩
        rw [hk] at hmod
        have h3 := h3 k
        omega
    omega
  · -- Reverse direction: if 3 ∣ n then 7 ∣ 2^n - 1
    intro hdiv
    have h1 : ∃ k, n = 3 * k := by
      obtain ⟨k, hk⟩ := hdiv
      exact ⟨k, by omega⟩
    rcases h1 with ⟨k, hk⟩
    rw [hk]
    have h2 : 2 ^ (3 * k) % 7 = 1 := h k
    have h3 : 7 ∣ 2 ^ (3 * k) - 1 := by
      have h4 : 2 ^ (3 * k) % 7 = 1 := h2
      have h5 : 2 ^ (3 * k) ≥ 1 := by
        apply Nat.one_le_pow
        omega
      omega
    exact h3

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  -- Show that 2^n mod 7 is never 6 (which would make 2^n + 1 ≡ 0 mod 7)
  have h : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ]
      simp [pow_add, pow_mul, Nat.pow_mod, ih, Nat.mul_mod]
      <;> norm_num
  have h2 : ∀ k : ℕ, 2 ^ (3 * k + 1) % 7 = 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Nat.add_assoc]
      simp [pow_add, pow_mul, Nat.pow_mod, ih, Nat.mul_mod]
      <;> norm_num
  have h3 : ∀ k : ℕ, 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Nat.add_assoc]
      simp [pow_add, pow_mul, Nat.pow_mod, ih, Nat.mul_mod]
      <;> norm_num
  intro hdiv
  have hmod : (2 ^ n + 1) % 7 = 0 := by
    have h1 : 7 ∣ 2 ^ n + 1 := hdiv
    have h2 : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h1
    exact h2
  -- Check all cases for n mod 3
  have hcase : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcase with (hcase | hcase | hcase)
  · -- Case n ≡ 0 (mod 3)
    have h1 : ∃ k, n = 3 * k := by
      use n / 3
      omega
    rcases h1 with ⟨k, hk⟩
    rw [hk] at hmod
    have h2 := h k
    omega
  · -- Case n ≡ 1 (mod 3)
    have h1 : ∃ k, n = 3 * k + 1 := by
      use n / 3
      omega
    rcases h1 with ⟨k, hk⟩
    rw [hk] at hmod
    have h2 := h2 k
    omega
  · -- Case n ≡ 2 (mod 3)
    have h1 : ∃ k, n = 3 * k + 2 := by
      use n / 3
      omega
    rcases h1 with ⟨k, hk⟩
    rw [hk] at hmod
    have h2 := h3 k
    omega
