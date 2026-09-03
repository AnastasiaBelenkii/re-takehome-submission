import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- Helper lemma to show no smaller positive integer satisfies the condition. -/
lemma no_smaller_solution : ∀ m, 0 < m → m < 19 → ¬ 77 ∣ (m + 2) * (m + 3) := by
  intro m h_pos h_lt
  interval_cases m <;> norm_num [Nat.dvd_iff_mod_eq_zero]

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Show 19 is in the set
    constructor
    · -- 0 < 19
      norm_num
    · -- 77 ∣ (19 + 2) * (19 + 3)
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Show 19 is the least
    intro m hm
    rcases hm with ⟨hm_pos, hm_dvd⟩
    by_contra h
    -- h : ¬ (19 ≤ m) implies m < 19
    have h_lt : m < 19 := Nat.not_le.mp h
    have h_not_dvd : ¬ 77 ∣ (m + 2) * (m + 3) := no_smaller_solution m hm_pos h_lt
    exact h_not_dvd hm_dvd
