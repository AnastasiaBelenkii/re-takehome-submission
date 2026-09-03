import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Prove 19 is in the set: 0 < 19 and 77 ∣ (19+2)*(19+3)
    simp [p07_answer]
    norm_num
  · -- Prove 19 is the least element
    intro m hm
    rcases hm with ⟨h_pos, h_dvd⟩
    -- We want to show 19 ≤ m.
    -- We prove this by showing that if m < 19, we get a contradiction.
    apply Nat.le_of_not_gt
    intro h_lt
    -- h_lt : m < 19
    -- We use interval_cases to check all values 0..18.
    -- interval_cases uses linarith to find bounds from context.
    -- h_lt provides the upper bound.
    interval_cases m <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h_dvd <;> contradiction
