import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20) := by
  constructor
  · -- First part: IsLeast for a^2 * b^5 case
    constructor
    · -- Show 10 is in the set
      refine' ⟨5, 2, by decide, by decide, _, rfl⟩
      norm_num [Nat.dvd_iff_mod_eq_zero]
    · -- Show 10 is minimal
      intro n hn hlt
      rcases hn with ⟨a, b, ha, hb, hdvd, rfl⟩
      have : 10 ≤ a * b := by
        -- Prime factorization analysis
        have h2000 : 2000 = 2^4 * 5^3 := by norm_num
        rw [h2000] at hdvd
        -- Analyze valuations at primes 2 and 5
        have h2 : 4 ≤ Nat.factorization (a^2 * b^5) 2 := by
          have := Nat.le_of_dvd (by positivity) hdvd
          simpa [h2000, Nat.factorization_pow, Nat.factorization_mul, Nat.factorization_prime_pow] using this
        have h5 : 3 ≤ Nat.factorization (a^2 * b^5) 5 := by
          have := Nat.le_of_dvd (by positivity) hdvd
          simpa [h2000, Nat.factorization_pow, Nat.factorization_mul, Nat.factorization_prime_pow] using this
        -- Extract constraints on exponents
        have h2_exp : 2 * Nat.factorization a 2 + 5 * Nat.factorization b 2 ≥ 4 := by
          simpa [Nat.factorization_pow, Nat.factorization_mul] using h2
        have h5_exp : 2 * Nat.factorization a 5 + 5 * Nat.factorization b 5 ≥ 3 := by
          simpa [Nat.factorization_pow, Nat.factorization_mul] using h5
        -- Prove minimum ab = 10
        have h_ab_ge_10 : 10 ≤ a * b := by
          by_contra h
          have h' : a * b ≤ 9 := by linarith
          -- Check all possibilities for small products
          have : a ≤ 9 := by nlinarith
          have : b ≤ 9 := by nlinarith
          interval_cases a <;> interval_cases b <;> norm_num at ha hb h2_exp h5_exp ⊢ <;>
            (try omega) <;> (try contradiction)
        exact h_ab_ge_10
      exact hlt.of_le this
  · -- Second part: IsLeast for a^3 * b^4 case
    constructor
    · -- Show 20 is in the set
      refine' ⟨5, 4, by decide, by decide, _, rfl⟩
      norm_num [Nat.dvd_iff_mod_eq_zero]
    · -- Show 20 is minimal
      intro n hn hlt
      rcases hn with ⟨a, b, ha, hb, hdvd, rfl⟩
      have : 20 ≤ a * b := by
        -- Prime factorization analysis
        have h2000 : 2000 = 2^4 * 5^3 := by norm_num
        rw [h2000] at hdvd
        -- Analyze valuations at primes 2 and 5
        have h2 : 4 ≤ Nat.factorization (a^3 * b^4) 2 := by
          have := Nat.le_of_dvd (by positivity) hdvd
          simpa [h2000, Nat.factorization_pow, Nat.factorization_mul, Nat.factorization_prime_pow] using this
        have h5 : 3 ≤ Nat.factorization (a^3 * b^4) 5 := by
          have := Nat.le_of_dvd (by positivity) hdvd
          simpa [h2000, Nat.factorization_pow, Nat.factorization_mul, Nat.factorization_prime_pow] using this
        -- Extract constraints on exponents
        have h2_exp : 3 * Nat.factorization a 2 + 4 * Nat.factorization b 2 ≥ 4 := by
          simpa [Nat.factorization_pow, Nat.factorization_mul] using h2
        have h5_exp : 3 * Nat.factorization a 5 + 4 * Nat.factorization b 5 ≥ 3 := by
          simpa [Nat.factorization_pow, Nat.factorization_mul] using h5
        -- Prove minimum ab = 20
        have h_ab_ge_20 : 20 ≤ a * b := by
          by_contra h
          have h' : a * b ≤ 19 := by linarith
          -- Check all possibilities for small products
          have : a ≤ 19 := by nlinarith
          have : b ≤ 19 := by nlinarith
          interval_cases a <;> interval_cases b <;> norm_num at ha hb h2_exp h5_exp ⊢ <;>
            (try omega) <;> (try contradiction)
        exact h_ab_ge_20
      exact hlt.of_le this
