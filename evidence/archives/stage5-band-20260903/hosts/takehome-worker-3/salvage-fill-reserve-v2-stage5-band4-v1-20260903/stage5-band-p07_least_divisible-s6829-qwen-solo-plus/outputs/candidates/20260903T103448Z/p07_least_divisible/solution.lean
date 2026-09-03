import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- 19 is in the set
    constructor
    · norm_num
    · norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- 19 is minimal
    intro m hm
    rcases hm with ⟨hm_pos, hm_dvd⟩
    by_contra h
    have h_lt : m < 19 := Nat.lt_of_not_ge h
    interval_cases m <;> norm_num [Nat.dvd_iff_mod_eq_zero] at hm_dvd <;> contradiction
