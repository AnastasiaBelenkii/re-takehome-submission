import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- Proof Sketch:
  -- 1. Verify 19 satisfies the condition (0 < 19 and 77 divides 21*22).
  -- 2. Assume m < 19 satisfies the condition and derive a contradiction.
  -- 3. Since m is a natural number, check all cases 1 <= m <= 18.
  
  constructor
  · -- Part 1: Show 19 is in the set
    simp [p07_answer]
    constructor
    · -- 0 < 19
      norm_num
    · -- 77 ∣ (19 + 2) * (19 + 3)
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Part 2: Show 19 is the least
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    -- hm : 0 < m ∧ 77 ∣ (m + 2) * (m + 3)
    -- Goal: 19 ≤ m
    by_contra h
    have h_lt : m < 19 := by omega
    -- Check all values from 1 to 18
    interval_cases m <;> norm_num [Nat.dvd_iff_mod_eq_zero] at hm <;> try contradiction
