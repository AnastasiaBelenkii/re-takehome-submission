import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- `19` belongs to the set.
  have h_mem : (0 < p07_answer) ∧ 77 ∣ (p07_answer + 2) * (p07_answer + 3) := by
    constructor
    · decide
    · norm_num
  refine ⟨h_mem, ?_⟩
  intro n hn
  rcases hn with ⟨hnpos, hdiv⟩
  -- prove that any such `n` is at least `19`
  by_contra hlt
  have hle : n ≤ 18 := Nat.le_of_lt_succ hlt
  interval_cases n using hle
  · -- the case `n = 0` contradicts `0 < n`
    cases hnpos
  all_goals
    have : ¬ 77 ∣ (n + 2) * (n + 3) := by norm_num
    exact this hdiv
