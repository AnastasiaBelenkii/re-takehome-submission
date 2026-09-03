import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- `19` belongs to the set.
  have hmem : p07_answer ∈ {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} := by
    have hpos : (0 : ℕ) < p07_answer := by decide
    have hdiv : 77 ∣ (p07_answer + 2) * (p07_answer + 3) := by
      norm_num
    exact ⟨hpos, hdiv⟩
  refine ⟨hmem, ?_⟩
  -- Minimality: any other element is at least `19`.
  intro n hn
  rcases hn with ⟨hpos, hdiv⟩
  by_contra hlt
  -- `hlt : ¬ 19 ≤ n`, hence `n < 19`.
  have hlt' : n < p07_answer := Nat.lt_of_not_ge hlt
  have hle18 : n ≤ 18 := Nat.le_of_lt_succ hlt'
  have : False := by
    interval_cases n using hle18
    all_goals
      have : ¬ (77 : ℕ) ∣ (n + 2) * (n + 3) := by
        norm_num
      exact this hdiv
  exact this
