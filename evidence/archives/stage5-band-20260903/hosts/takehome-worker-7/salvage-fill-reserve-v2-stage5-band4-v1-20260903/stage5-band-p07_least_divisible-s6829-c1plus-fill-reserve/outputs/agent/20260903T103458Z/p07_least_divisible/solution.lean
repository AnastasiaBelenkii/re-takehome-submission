import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- Part 1: Show 19 is in the set
  have h_mem : (0 < (p07_answer : ℕ)) ∧ 77 ∣ (p07_answer + 2) * (p07_answer + 3) := by
    constructor
    · decide
    · norm_num [Nat.dvd_iff_mod_eq_zero]
  
  refine ⟨h_mem, ?_⟩
  intro n hn
  rcases hn with ⟨hnpos, hndiv⟩
  -- suppose n < 19, derive contradiction
  by_contra hnot
  have hlt : n < p07_answer := Nat.lt_of_not_ge hnot
  -- Check each case from 1 to 18
  interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at hndiv <;> omega
