import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- Unfold p07_answer to 19 explicitly to ensure numerical literals are visible
  unfold p07_answer
  constructor
  · -- Part 1: Verify 19 is in the set
    constructor
    · -- Check 0 < 19
      norm_num
    · -- Check 77 ∣ (19 + 2) * (19 + 3)
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Part 2: Verify 19 is the least
    intro m hm
    -- hm : 0 < m ∧ 77 ∣ (m + 2) * (m + 3)
    -- We assume m < 19 and derive a contradiction
    by_contra h
    have h_lt : m < 19 := Nat.not_le.mp h
    -- Use interval_cases to check all m from 0 to 18
    -- h_lt provides the upper bound for interval_cases
    interval_cases m <;> norm_num [Nat.dvd_iff_mod_eq_zero] at * <;> contradiction
