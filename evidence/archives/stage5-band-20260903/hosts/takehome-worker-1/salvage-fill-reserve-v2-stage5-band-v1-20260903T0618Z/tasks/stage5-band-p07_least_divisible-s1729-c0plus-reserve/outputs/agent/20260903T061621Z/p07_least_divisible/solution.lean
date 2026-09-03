import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Part 1: Show 19 is in the set
    simp [p07_answer]
    norm_num
  · -- Part 2: Show 19 is the least element
    intro b hb
    simp only [Set.mem_setOf_eq, p07_answer] at hb ⊢
    -- hb : 0 < b ∧ 77 ∣ (b + 2) * (b + 3)
    -- Goal: 19 ≤ b
    by_contra h
    have hb_lt : b < 19 := by omega
    -- Check all cases from 1 to 18
    interval_cases b <;> 
      simp_all [Nat.dvd_iff_mod_eq_zero] <;>
      norm_num <;>
      contradiction
