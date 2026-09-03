import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Show 19 is in the set: 0 < 19 and 77 ∣ (19+2)*(19+3) = 21*22 = 462
    constructor
    · norm_num
    · norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Show nothing smaller works
    intro n hn
    have h₁ : 0 < n := hn.1
    have h₂ : 77 ∣ (n + 2) * (n + 3) := hn.2
    -- We want to show 19 ≤ n.
    -- Assume n < 19 and derive contradiction.
    by_contra h
    have h_lt : n < 19 := lt_of_not_ge h
    interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h₂ <;> contradiction
