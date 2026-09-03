import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Part 1: Prove 19 is in the set
    constructor
    · -- 0 < 19
      norm_num
    · -- 77 ∣ (19 + 2) * (19 + 3)
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Part 2: Prove 19 is a lower bound
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    obtain ⟨h₁, h₂⟩ := hm
    by_contra h
    -- If 19 is not ≤ m, then m < 19
    have h₃ : m < 19 := lt_of_not_ge h
    -- Check all possible values from 1 to 18
    interval_cases m <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h₁ h₂ <;> contradiction
