import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Show 19 ∈ S: 0 < 19 and 77 ∣ (19+2)*(19+3)
    refine' ⟨by decide, _⟩
    norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Show 19 is a lower bound: for all n ∈ S, 19 ≤ n
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra h
    -- If n < 19, then n ≤ 18
    have h_bound : n < 19 := by exact lt_of_not_ge h
    -- Check all n from 1 to 18
    interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at hn <;> cases hn <;> contradiction
