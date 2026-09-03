import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Prove 19 is in the set
    norm_num [p07_answer]
  · -- Prove 19 is the least element
    intro m hm
    rcases hm with ⟨hpos, hdiv⟩
    by_cases h : m < 19
    · -- Case m < 19
      have : ∀ k < 19, ¬ 77 ∣ (k + 2) * (k + 3) := by decide
      have h_false : ¬ 77 ∣ (m + 2) * (m + 3) := this m h
      contradiction
    · -- Case m ≥ 19
      exact Nat.le_of_not_lt h
