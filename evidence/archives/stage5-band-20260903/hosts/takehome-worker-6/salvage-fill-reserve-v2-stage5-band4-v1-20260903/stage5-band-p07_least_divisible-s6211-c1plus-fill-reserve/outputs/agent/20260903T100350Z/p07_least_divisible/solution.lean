import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Part 1: 19 ∈ S
    constructor
    · -- 0 < 19
      norm_num
    · -- 77 ∣ (19 + 2) * (19 + 3)
      norm_num [Nat.dvd_iff_mod_eq_zero]
      <;> decide
  · -- Part 2: Minimality
    intro x hx
    by_contra h
    have hlt : x < 19 := lt_of_not_ge h
    have hpos : 0 < x := hx.1
    have hdiv : 77 ∣ (x + 2) * (x + 3) := hx.2
    have hbound : x ≤ 18 := Nat.lt_succ_iff.mp hlt
    interval_cases x <;> norm_num [Nat.dvd_iff_mod_eq_zero] at hdiv <;> contradiction
