import Mathlib

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- Part 1: IsLeast {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10
    constructor
    · -- Show 10 is in the set
      -- Witness: a = 1, b = 10. 1^2 * 10^5 = 100000 = 2000 * 50.
      refine' ⟨1, ⟨10, ⟨by decide, ⟨by decide, _, rfl⟩⟩⟩⟩
      norm_num [Nat.dvd_iff_mod_eq_zero]
    · -- Show 10 is the least element
      intro n hn
      by_contra h
      push Not at h
      -- h : n < 10
      rcases hn with ⟨a, b, ha, hb, hdiv, hn⟩
      rw [hn] at h
      have h_ab_lt : a * b < 10 := h
      have h_a_lt : a < 10 := by nlinarith [ha, hb, h_ab_lt]
      have h_b_lt : b < 10 := by nlinarith [ha, hb, h_ab_lt]
      interval_cases a <;> interval_cases b <;>
        simp_all [Nat.dvd_iff_mod_eq_zero]
        <;> norm_num at hdiv
        <;> try contradiction
  · -- Part 2: IsLeast {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10
    constructor
    · -- Show 10 is in the set
      -- Witness: a = 5, b = 2. 5^3 * 2^4 = 125 * 16 = 2000.
      refine' ⟨5, ⟨2, ⟨by decide, ⟨by decide, _, rfl⟩⟩⟩⟩
      norm_num [Nat.dvd_iff_mod_eq_zero]
    · -- Show 10 is the least element
      intro n hn
      by_contra h
      push Not at h
      -- h : n < 10
      rcases hn with ⟨a, b, ha, hb, hdiv, hn⟩
      rw [hn] at h
      have h_ab_lt : a * b < 10 := h
      have h_a_lt : a < 10 := by nlinarith [ha, hb, h_ab_lt]
      have h_b_lt : b < 10 := by nlinarith [ha, hb, h_ab_lt]
      interval_cases a <;> interval_cases b <;>
        simp_all [Nat.dvd_iff_mod_eq_zero]
        <;> norm_num at hdiv
        <;> try contradiction
