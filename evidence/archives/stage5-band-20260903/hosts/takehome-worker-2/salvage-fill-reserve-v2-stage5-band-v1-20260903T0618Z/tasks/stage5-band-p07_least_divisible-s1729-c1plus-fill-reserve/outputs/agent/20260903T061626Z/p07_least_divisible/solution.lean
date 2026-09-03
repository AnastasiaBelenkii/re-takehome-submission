import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Part 1: Show 19 is in the set
    constructor
    · -- 0 < 19
      norm_num
    · -- 77 ∣ (19 + 2) * (19 + 3)
      rw [Nat.dvd_iff_mod_eq_zero]
      norm_num
  · -- Part 2: Show 19 is a lower bound
    intro n hn
    by_contra h_not_le
    have h_lt : n < 19 := lt_of_not_ge h_not_le
    have h_pos : 0 < n := hn.1
    have h_div : 77 ∣ (n + 2) * (n + 3) := hn.2
    -- split into the finitely many possibilities for `n`
    interval_cases n
    all_goals
      rw [Nat.dvd_iff_mod_eq_zero] at h_div
      norm_num
