import Mathlib.Tactic

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_cycle : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero =>
      constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
    | succ k ih =>
      constructor
      · -- 2^(3*(k+1)) = 2^(3*k + 3) = 2^(3*k) * 8 ≡ 1 * 1 = 1 (mod 7)
        have h1 : 2 ^ (3 * k) % 7 = 1 := ih.1
        have h2 : 2 ^ (3 * k + 1) % 7 = 2 := ih.2.1
        have h3 : 2 ^ (3 * k + 2) % 7 = 4 := ih.2.2
        calc
          2 ^ (3 * (k + 1)) % 7 = 2 ^ (3 * k + 3) % 7 := by ring_nf
          _ = (2 ^ (3 * k) * 2 ^ 3) % 7 := by rw [pow_add]
          _ = ((2 ^ (3 * k) % 7) * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
          _ = (1 * 1) % 7 := by rw [h1]; norm_num
          _ = 1 := by norm_num
      · constructor
        · -- 2^(3*(k+1)+1) = 2^(3*k + 4) = 2^(3*k) * 16 ≡ 1 * 2 = 2 (mod 7)
          have h1 : 2 ^ (3 * k) % 7 = 1 := ih.1
          have h2 : 2 ^ (3 * k + 1) % 7 = 2 := ih.2.1
          have h3 : 2 ^ (3 * k + 2) % 7 = 4 := ih.2.2
          calc
            2 ^ (3 * (k + 1) + 1) % 7 = 2 ^ (3 * k + 4) % 7 := by ring_nf
            _ = (2 ^ (3 * k) * 2 ^ 4) % 7 := by rw [pow_add]
            _ = ((2 ^ (3 * k) % 7) * (2 ^ 4 % 7)) % 7 := by simp [Nat.mul_mod]
            _ = (1 * 2) % 7 := by rw [h1]; norm_num
            _ = 2 := by norm_num
        · -- 2^(3*(k+1)+2) = 2^(3*k + 5) = 2^(3*k) * 32 ≡ 1 * 4 = 4 (mod 7)
          have h1 : 2 ^ (3 * k) % 7 = 1 := ih.1
          have h2 : 2 ^ (3 * k + 1) % 7 = 2 := ih.2.1
          have h3 : 2 ^ (3 * k + 2) % 7 = 4 := ih.2.2
          calc
            2 ^ (3 * (k + 1) + 2) % 7 = 2 ^ (3 * k + 5) % 7 := by ring_nf
            _ = (2 ^ (3 * k) * 2 ^ 5) % 7 := by rw [pow_add]
            _ = ((2 ^ (3 * k) % 7) * (2 ^ 5 % 7)) % 7 := by simp [Nat.mul_mod]
            _ = (1 * 4) % 7 := by rw [h1]; norm_num
            _ = 4 := by norm_num
  
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h₁ : 2 ^ n % 7 = 1 := by
      have h₂ : 7 ∣ 2 ^ n - 1 := h
      have h₃ : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      have h₄ : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h₂
      have h₅ : 2 ^ n % 7 = 1 := by
        have h₆ : 2 ^ n % 7 = (2 ^ n - 1 + 1) % 7 := by
          rw [Nat.add_comm]
          <;> omega
        rw [h₆]
        have h₇ : (2 ^ n - 1 + 1) % 7 = (0 + 1) % 7 := by
          rw [← Nat.mod_add_div (2 ^ n - 1) 7]
          simp [h₄]
          <;> omega
        omega
      exact h₅
    -- Now show that if 2^n ≡ 1 (mod 7), then 3 ∣ n
    have h₂ : 3 ∣ n := by
      by_contra h₃
      -- If 3 does not divide n, then n ≡ 1 or 2 (mod 3)
      have h₄ : n % 3 = 1 ∨ n % 3 = 2 := by
        have h₅ : n % 3 ≠ 0 := by
          intro h₆
          have h₇ : 3 ∣ n := by
            omega
          contradiction
        have h₆ : n % 3 = 1 ∨ n % 3 = 2 := by
          have h₇ : n % 3 < 3 := Nat.mod_lt n (by norm_num)
          have h₈ : n % 3 ≥ 0 := by omega
          omega
        exact h₆
      cases h₄ with
      | inl h₄ =>
        -- Case n ≡ 1 (mod 3)
        have h₅ : ∃ k : ℕ, n = 3 * k + 1 := by
          use n / 3
          have h₆ := Nat.div_add_mod n 3
          omega
        rcases h₅ with ⟨k, rfl⟩
        have h₆ := h_cycle k
        have h₇ : 2 ^ (3 * k + 1) % 7 = 2 := h₆.2.1
        omega
      | inr h₄ =>
        -- Case n ≡ 2 (mod 3)
        have h₅ : ∃ k : ℕ, n = 3 * k + 2 := by
          use n / 3
          have h₆ := Nat.div_add_mod n 3
          omega
        rcases h₅ with ⟨k, rfl⟩
        have h₆ := h_cycle k
        have h₇ : 2 ^ (3 * k + 2) % 7 = 4 := h₆.2.2
        omega
    exact h₂
  · -- Backward direction: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    have h₁ : ∃ k : ℕ, n = 3 * k := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by omega⟩
    rcases h₁ with ⟨k, rfl⟩
    have h₂ := h_cycle k
    have h₃ : 2 ^ (3 * k) % 7 = 1 := h₂.1
    have h₄ : 2 ^ (3 * k) ≥ 1 := by
      apply Nat.one_le_pow
      omega
    have h₅ : 7 ∣ 2 ^ (3 * k) - 1 := by
      have h₆ : (2 ^ (3 * k) - 1) % 7 = 0 := by
        have h₇ : 2 ^ (3 * k) % 7 = 1 := h₃
        have h₈ : 2 ^ (3 * k) ≥ 1 := h₄
        omega
      exact Nat.dvd_of_mod_eq_zero h₆
    exact h₅

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  have h_cycle : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero =>
      constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
    | succ k ih =>
      constructor
      · -- 2^(3*(k+1)) = 2^(3*k + 3) = 2^(3*k) * 8 ≡ 1 * 1 = 1 (mod 7)
        have h1 : 2 ^ (3 * k) % 7 = 1 := ih.1
        calc
          2 ^ (3 * (k + 1)) % 7 = 2 ^ (3 * k + 3) % 7 := by ring_nf
          _ = (2 ^ (3 * k) * 2 ^ 3) % 7 := by rw [pow_add]
          _ = ((2 ^ (3 * k) % 7) * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
          _ = (1 * 1) % 7 := by rw [h1]; norm_num
          _ = 1 := by norm_num
      · constructor
        · -- 2^(3*(k+1)+1) = 2^(3*k + 4) = 2^(3*k) * 16 ≡ 1 * 2 = 2 (mod 7)
          have h1 : 2 ^ (3 * k) % 7 = 1 := ih.1
          calc
            2 ^ (3 * (k + 1) + 1) % 7 = 2 ^ (3 * k + 4) % 7 := by ring_nf
            _ = (2 ^ (3 * k) * 2 ^ 4) % 7 := by rw [pow_add]
            _ = ((2 ^ (3 * k) % 7) * (2 ^ 4 % 7)) % 7 := by simp [Nat.mul_mod]
            _ = (1 * 2) % 7 := by rw [h1]; norm_num
            _ = 2 := by norm_num
        · -- 2^(3*(k+1)+2) = 2^(3*k + 5) = 2^(3*k) * 32 ≡ 1 * 4 = 4 (mod 7)
          have h1 : 2 ^ (3 * k) % 7 = 1 := ih.1
          calc
            2 ^ (3 * (k + 1) + 2) % 7 = 2 ^ (3 * k + 5) % 7 := by ring_nf
            _ = (2 ^ (3 * k) * 2 ^ 5) % 7 := by rw [pow_add]
            _ = ((2 ^ (3 * k) % 7) * (2 ^ 5 % 7)) % 7 := by simp [Nat.mul_mod]
            _ = (1 * 4) % 7 := by rw [h1]; norm_num
            _ = 4 := by norm_num
  
  intro h
  have h₁ : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  have h₂ : 2 ^ n % 7 = 6 := by
    have h₃ : (2 ^ n + 1) % 7 = 0 := h₁
    have h₄ : 2 ^ n % 7 = 6 := by
      have h₅ : (2 ^ n + 1) % 7 = ((2 ^ n % 7) + 1) % 7 := by simp [Nat.add_mod]
      rw [h₅] at h₃
      have h₆ : ((2 ^ n % 7) + 1) % 7 = 0 := h₃
      have h₇ : 2 ^ n % 7 < 7 := Nat.mod_lt _ (by norm_num)
      have h₈ : 2 ^ n % 7 ≥ 0 := by omega
      interval_cases 2 ^ n % 7 <;> omega
    exact h₄
  
  -- Show that 2^n % 7 cannot be 6
  have h₃ : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
    have h₄ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    cases h₄ with
    | inl h₄ =>
      -- Case n ≡ 0 (mod 3)
      have h₅ : ∃ k : ℕ, n = 3 * k := by
        use n / 3
        have h₆ := Nat.div_add_mod n 3
        omega
      rcases h₅ with ⟨k, rfl⟩
      have h₆ := h_cycle k
      exact Or.inl h₆.1
    | inr h₄ =>
      cases h₄ with
      | inl h₄ =>
        -- Case n ≡ 1 (mod 3)
        have h₅ : ∃ k : ℕ, n = 3 * k + 1 := by
          use n / 3
          have h₆ := Nat.div_add_mod n 3
          omega
        rcases h₅ with ⟨k, rfl⟩
        have h₆ := h_cycle k
        exact Or.inr (Or.inl h₆.2.1)
      | inr h₄ =>
        -- Case n ≡ 2 (mod 3)
        have h₅ : ∃ k : ℕ, n = 3 * k + 2 := by
          use n / 3
          have h₆ := Nat.div_add_mod n 3
          omega
        rcases h₅ with ⟨k, rfl⟩
        have h₆ := h_cycle k
        exact Or.inr (Or.inr h₆.2.2)
  
  -- Contradiction: 2^n % 7 cannot be 6
  cases h₃ with
  | inl h₃ =>
    omega
  | inr h₃ =>
    cases h₃ with
    | inl h₃ =>
      omega
    | inr h₃ =>
      omega
