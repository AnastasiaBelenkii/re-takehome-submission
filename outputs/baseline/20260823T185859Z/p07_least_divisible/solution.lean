import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Prove p07_answer is in the set
    simp [p07_answer]
    <;> norm_num
  · -- Prove p07_answer is the least element
    intro n hn
    have h_pos : 0 < n := hn.1
    have h_dvd : 77 ∣ (n + 2) * (n + 3) := hn.2
    by_contra h
    have h_lt : n < 19 := lt_of_not_ge h
    interval_cases n <;> 
      norm_num [Nat.dvd_iff_mod_eq_zero] at h_dvd <;> 
      omega
