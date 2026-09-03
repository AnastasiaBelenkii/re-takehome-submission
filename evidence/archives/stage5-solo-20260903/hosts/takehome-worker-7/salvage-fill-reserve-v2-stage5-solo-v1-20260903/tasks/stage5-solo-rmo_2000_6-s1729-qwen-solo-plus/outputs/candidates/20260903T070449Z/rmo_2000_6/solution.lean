import Mathlib

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- Part 1: IsLeast for a^2 * b^5
    constructor
    · -- Existence: 10 is in the set
      use 1, 10
      constructor
      · decide
      constructor
      · decide
      constructor
      · rw [Nat.dvd_iff_mod_eq_zero]
        norm_num
      · rfl
    · -- Minimality: Any element in the set is >= 10
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h_min : 10 ≤ a * b := by
        by_contra h_lt
        have h_ab_le_9 : a * b ≤ 9 := by linarith
        have h_a_le_9 : a ≤ 9 := by
          have : a ≤ a * b := Nat.le_mul_of_pos_right a hb
          linarith
        have h_b_le_9 : b ≤ 9 := by
          have : b ≤ a * b := Nat.le_mul_of_pos_left b ha
          linarith
        interval_cases a <;>
          interval_cases b <;>
            rw [Nat.dvd_iff_mod_eq_zero] at hdiv <;>
            norm_num at hdiv <;>
            omega
      exact h_min
  · -- Part 2: IsLeast for a^3 * b^4
    constructor
    · -- Existence: 10 is in the set
      use 5, 2
      constructor
      · decide
      constructor
      · decide
      constructor
      · rw [Nat.dvd_iff_mod_eq_zero]
        norm_num
      · rfl
    · -- Minimality: Any element in the set is >= 10
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h_min : 10 ≤ a * b := by
        by_contra h_lt
        have h_ab_le_9 : a * b ≤ 9 := by linarith
        have h_a_le_9 : a ≤ 9 := by
          have : a ≤ a * b := Nat.le_mul_of_pos_right a hb
          linarith
        have h_b_le_9 : b ≤ 9 := by
          have : b ≤ a * b := Nat.le_mul_of_pos_left b ha
          linarith
        interval_cases a <;>
          interval_cases b <;>
            rw [Nat.dvd_iff_mod_eq_zero] at hdiv <;>
            norm_num at hdiv <;>
            omega
      exact h_min
