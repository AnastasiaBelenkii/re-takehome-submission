import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Show 19 is in the set
    dsimp [p07_answer]
    constructor
    · norm_num
    · norm_num
  · -- Show 19 is a lower bound
    intro n hn
    cases' hn with h_pos h_div
    -- Goal: 19 ≤ n
    by_contra h_not_le
    have h_lt : n < 19 := Nat.lt_of_not_ge h_not_le
    -- Use decide to check all n < 19
    have h_dec : ∀ m : ℕ, m < 19 → ¬ 77 ∣ (m + 2) * (m + 3) := by decide
    exact h_dec n h_lt h_div
