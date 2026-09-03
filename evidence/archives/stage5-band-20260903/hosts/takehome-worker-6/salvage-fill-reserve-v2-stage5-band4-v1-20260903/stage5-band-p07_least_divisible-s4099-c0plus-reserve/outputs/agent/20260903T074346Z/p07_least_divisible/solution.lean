import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Prove 19 is in the set
    dsimp [p07_answer]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Prove 19 is a lower bound
    intro b hb
    have h_pos : 0 < b := hb.1
    have h_dvd : 77 ∣ (b + 2) * (b + 3) := hb.2
    have h_ge : 19 ≤ b := by
      by_contra h
      have h_lt : b < 19 := Nat.lt_of_not_ge h
      interval_cases b <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h_dvd <;> contradiction
    exact h_ge
