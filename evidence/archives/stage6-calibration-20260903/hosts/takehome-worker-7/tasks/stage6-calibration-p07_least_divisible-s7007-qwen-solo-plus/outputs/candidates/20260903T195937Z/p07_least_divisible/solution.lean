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
    simp [p07_answer]
    norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Prove 19 is the least element
    intro m hm
    cases hm with
    | intro h_pos h_dvd =>
      by_contra h_not_ge
      have h_lt : m < 19 := Nat.not_le.mp h_not_ge
      interval_cases m <;>
        norm_num [Nat.dvd_iff_mod_eq_zero] at h_pos h_dvd <;>
        contradiction
