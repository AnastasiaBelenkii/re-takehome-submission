import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  refine ⟨?mem, ?least⟩
  · -- `19` satisfies the condition
    have hpos : (0 : ℕ) < 19 := by decide
    have hdiv : 77 ∣ (19 + 2) * (19 + 3) := by norm_num
    exact ⟨hpos, hdiv⟩
  · -- minimality
    intro n hn
    rcases hn with ⟨hnpos, hdiv⟩
    have hnot :
        ¬ ∃ n : ℕ, n < 19 ∧ 0 < n ∧ 77 ∣ (n + 2) * (n + 3) := by
      decide
    have : 19 ≤ n := by
      by_contra hlt
      have hlt' : n < 19 := lt_of_not_ge hlt
      have : ∃ n : ℕ, n < 19 ∧ 0 < n ∧ 77 ∣ (n + 2) * (n + 3) :=
        ⟨n, hlt', hnpos, hdiv⟩
      exact hnot this
    exact this
