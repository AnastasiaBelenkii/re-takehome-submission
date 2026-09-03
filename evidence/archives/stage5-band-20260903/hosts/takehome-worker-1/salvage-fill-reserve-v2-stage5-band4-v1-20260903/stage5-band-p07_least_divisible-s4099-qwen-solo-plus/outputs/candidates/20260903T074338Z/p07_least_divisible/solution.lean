import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · constructor
    · -- Show 0 < 19
      norm_num [p07_answer]
    · -- Show 77 ∣ (19+2)*(19+3)
      norm_num [p07_answer, Nat.dvd_iff_mod_eq_zero]
  · -- Show minimality: any n in S must satisfy 19 ≤ n
    intro n hn
    by_contra h
    have hlt : n < 19 := Nat.lt_of_not_ge h
    interval_cases n <;> cases hn <;> norm_num [Nat.dvd_iff_mod_eq_zero] at * <;> contradiction
