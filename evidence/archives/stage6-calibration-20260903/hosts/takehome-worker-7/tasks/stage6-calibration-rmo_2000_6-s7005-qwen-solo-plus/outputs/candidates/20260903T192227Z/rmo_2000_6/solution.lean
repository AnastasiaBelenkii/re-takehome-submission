import Mathlib

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- Part 1: IsLeast for a^2 * b^5
    constructor
    · -- Existence: Show 10 is achievable
      use 1, 10
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num [Nat.dvd_iff_mod_eq_zero]
      · norm_num
    · -- Minimality: Show any n in set is >= 10
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      by_contra h
      have h_lt : a * b ≤ 9 := by linarith
      have h_a_le : a ≤ 9 := by
        have : 0 < a := ha
        nlinarith
      have h_b_le : b ≤ 9 := by
        have : 0 < b := hb
        nlinarith
      interval_cases a <;> interval_cases b <;>
        (try omega) <;> (try { norm_num at hdiv; contradiction })
  · -- Part 2: IsLeast for a^3 * b^4
    constructor
    · -- Existence: Show 10 is achievable
      use 5, 2
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num [Nat.dvd_iff_mod_eq_zero]
      · norm_num
    · -- Minimality: Show any n in set is >= 10
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      by_contra h
      have h_lt : a * b ≤ 9 := by linarith
      have h_a_le : a ≤ 9 := by
        have : 0 < a := ha
        nlinarith
      have h_b_le : b ≤ 9 := by
        have : 0 < b := hb
        nlinarith
      interval_cases a <;> interval_cases b <;>
        (try omega) <;> (try { norm_num at hdiv; contradiction })
