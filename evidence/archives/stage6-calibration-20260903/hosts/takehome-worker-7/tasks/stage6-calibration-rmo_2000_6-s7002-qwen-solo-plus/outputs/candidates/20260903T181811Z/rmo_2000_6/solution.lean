import Mathlib

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- Part 1: IsLeast for first set
    constructor
    · -- Show 10 is in the set
      use 1, 10
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · rfl
    · -- Show 10 is minimal
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, heq⟩
      rw [heq]
      by_contra h
      have h_lt : a * b < 10 := by linarith
      have h_a_le : a ≤ 9 := by
        by_contra h'
        have : a ≥ 10 := by omega
        have : a * b ≥ 10 := by nlinarith [hb]
        linarith
      have h_b_le : b ≤ 9 := by
        by_contra h'
        have : b ≥ 10 := by omega
        have : a * b ≥ 10 := by nlinarith [ha]
        linarith
      interval_cases a <;> interval_cases b <;>
        (try omega) <;>
        (try norm_num at hdiv ⊢) <;>
        (try contradiction)
  · -- Part 2: IsLeast for second set
    constructor
    · -- Show 10 is in the set
      use 5, 2
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · rfl
    · -- Show 10 is minimal
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, heq⟩
      rw [heq]
      by_contra h
      have h_lt : a * b < 10 := by linarith
      have h_a_le : a ≤ 9 := by
        by_contra h'
        have : a ≥ 10 := by omega
        have : a * b ≥ 10 := by nlinarith [hb]
        linarith
      have h_b_le : b ≤ 9 := by
        by_contra h'
        have : b ≥ 10 := by omega
        have : a * b ≥ 10 := by nlinarith [ha]
        linarith
      interval_cases a <;> interval_cases b <;>
        (try omega) <;>
        (try norm_num at hdiv ⊢) <;>
        (try contradiction)
