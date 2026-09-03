import Mathlib

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- Part 1: a²b⁵ divisible by 2000
    refine' ⟨⟨1, 10, by decide, by decide, _, rfl⟩, _⟩
    · -- Existence: 10 is in the set
      norm_num
    · -- Minimality: any element in the set is ≥ 10
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      by_contra h
      have h_lt : a * b < 10 := by omega
      have h_a : a < 10 := by
        have : 1 ≤ b := by linarith
        nlinarith
      have h_b : b < 10 := by
        have : 1 ≤ a := by linarith
        nlinarith
      interval_cases a <;>
        (try omega) <;>
        (try {
          interval_cases b <;>
            (try omega) <;>
            (try {
              norm_num at hdiv ⊢
              <;> omega
            })
        })
  · -- Part 2: a³b⁴ divisible by 2000
    refine' ⟨⟨1, 10, by decide, by decide, _, rfl⟩, _⟩
    · -- Existence: 10 is in the set
      norm_num
    · -- Minimality: any element in the set is ≥ 10
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      by_contra h
      have h_lt : a * b < 10 := by omega
      have h_a : a < 10 := by
        have : 1 ≤ b := by linarith
        nlinarith
      have h_b : b < 10 := by
        have : 1 ≤ a := by linarith
        nlinarith
      interval_cases a <;>
        (try omega) <;>
        (try {
          interval_cases b <;>
            (try omega) <;>
            (try {
              norm_num at hdiv ⊢
              <;> omega
            })
        })
