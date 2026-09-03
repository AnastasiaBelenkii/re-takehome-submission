import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Show p07_answer is in the set
    constructor
    · -- 0 < 19
      norm_num [p07_answer]
    · -- 77 ∣ (19 + 2) * (19 + 3)
      norm_num [p07_answer, Nat.dvd_iff_mod_eq_zero]
  · -- Show p07_answer is a lower bound
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    rcases hm with ⟨h_pos, h_dvd⟩
    by_contra h_not_le
    have h_lt : m < 19 := Nat.lt_of_not_ge h_not_le
    -- Use decide to verify that no m < 19 satisfies the divisibility condition
    -- This avoids manual case splitting and ensures correctness via computation
    have h_min : ∀ k < 19, ¬ 77 ∣ (k + 2) * (k + 3) := by decide
    exact h_min m h_lt h_dvd
