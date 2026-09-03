import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- Helper lemma to show that for n < 19, 77 does not divide (n + 2) * (n + 3). -/
lemma not_dvd_lt_19 (n : ℕ) (h : n < 19) : ¬ 77 ∣ (n + 2) * (n + 3) := by
  interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero]

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Prove 19 is in the set
    simp [p07_answer]
    norm_num
  · -- Prove minimality
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    have h_lt : n < 19 := Nat.lt_of_not_ge h
    have h_not_dvd := not_dvd_lt_19 n h_lt
    exact h_not_dvd hn_div
