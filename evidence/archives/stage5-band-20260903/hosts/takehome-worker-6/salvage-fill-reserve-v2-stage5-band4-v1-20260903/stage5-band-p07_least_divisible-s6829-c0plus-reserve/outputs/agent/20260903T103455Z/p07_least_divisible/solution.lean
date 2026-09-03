import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Show 19 ∈ {n | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)}
    constructor
    · -- Show 0 < 19
      norm_num
    · -- Show 77 ∣ (19 + 2) * (19 + 3)
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Show 19 is minimal
    intro n hn
    have h_pos : 0 < n := hn.1
    have h_dvd : 77 ∣ (n + 2) * (n + 3) := hn.2
    have h_ge : 19 ≤ n := by
      by_contra h
      have h_lt : n < 19 := not_le.mp h
      interval_cases n <;> 
        simp_all [Nat.dvd_iff_mod_eq_zero]
        <;> norm_num at *
        <;> contradiction
    exact h_ge
