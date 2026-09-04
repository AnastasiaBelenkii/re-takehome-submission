import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Part 1: Verify 19 satisfies the condition (positive and divisible)
    refine ⟨by decide, by decide⟩
  · -- Part 2: Prove minimality by showing no smaller positive integer works
    intro n hn
    rcases hn with ⟨hn_pos, hn_dvd⟩
    apply Nat.le_of_not_lt
    intro h_lt
    rw [p07_answer] at h_lt
    have h_le : n ≤ 18 := Nat.le_of_lt_succ h_lt
    interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at hn_dvd <;> contradiction
