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
    constructor
    · -- 0 < 19
      decide
    · -- 77 ∣ 21 * 22
      decide
  · -- Prove p07_answer is the least element
    intro m hm
    have h_pos : 0 < m := hm.1
    have h_dvd : 77 ∣ (m + 2) * (m + 3) := hm.2
    have h_ge : 19 ≤ m := by
      by_contra h
      have h_lt : m < 19 := Nat.lt_of_not_ge h
      interval_cases m <;>
        (try { norm_num at h_pos; contradiction })
        <;>
        (try { norm_num [Nat.dvd_iff_mod_eq_zero] at h_dvd; contradiction })
    exact h_ge
