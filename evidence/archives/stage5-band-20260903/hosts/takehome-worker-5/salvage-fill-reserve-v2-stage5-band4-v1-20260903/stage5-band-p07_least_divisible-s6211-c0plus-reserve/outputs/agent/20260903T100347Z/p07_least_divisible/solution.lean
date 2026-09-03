import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Part 1: Show 19 ∈ S
    constructor
    · -- 0 < 19
      norm_num
    · -- 77 ∣ (19 + 2) * (19 + 3)
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Part 2: Show 19 is minimal
    intro m hm
    by_contra h
    -- h : ¬ (19 ≤ m)
    have h_lt : m < 19 := lt_of_not_ge h
    -- Case analysis on m from 0 to 18
    interval_cases m <;> simp_all [Set.mem_setOf_eq] <;> norm_num [Nat.dvd_iff_mod_eq_zero] at * <;> contradiction
