import Mathlib

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- First part: IsLeast for a^2 * b^5 divisible by 2000
    constructor
    · -- Show 10 is in the set
      refine ⟨1, 10, by decide, by decide, by decide, rfl⟩
    · -- Show 10 is the least element
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h : 10 ≤ a * b := by
        by_contra h_lt
        have h_ab : a * b ≤ 9 := by linarith
        have h_a : a ≤ 9 := by nlinarith
        have h_b : b ≤ 9 := by nlinarith
        interval_cases a <;> interval_cases b <;>
          (try linarith) <;>
          (try {
            norm_num [Nat.dvd_iff_mod_eq_zero] at hdiv
            <;> contradiction
          })
      exact h
  · -- Second part: IsLeast for a^3 * b^4 divisible by 2000
    constructor
    · -- Show 10 is in the set
      refine ⟨5, 2, by decide, by decide, by decide, rfl⟩
    · -- Show 10 is the least element
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h : 10 ≤ a * b := by
        by_contra h_lt
        have h_ab : a * b ≤ 9 := by linarith
        have h_a : a ≤ 9 := by nlinarith
        have h_b : b ≤ 9 := by nlinarith
        interval_cases a <;> interval_cases b <;>
          (try linarith) <;>
          (try {
            norm_num [Nat.dvd_iff_mod_eq_zero] at hdiv
            <;> contradiction
          })
      exact h
