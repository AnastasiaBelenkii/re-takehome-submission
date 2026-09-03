import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- First, show that `p07_answer` itself belongs to the set.
  have hmem : (0 : ℕ) < p07_answer ∧ 77 ∣ (p07_answer + 2) * (p07_answer + 3) := by
    dsimp [p07_answer]
    constructor
    · norm_num
    · norm_num
  refine ⟨hmem, ?_⟩
  intro n hn
  -- Prove that any other element `n` of the set satisfies `19 ≤ n`.
  have hmin : 19 ≤ n := by
    by_contra hlt
    -- From `¬ 19 ≤ n` we get `n < 19`.
    have hlt' : n < 19 := lt_of_not_ge hlt
    -- Build a counterexample to the decidable statement that no `n < 19` works.
    have h_ex : ∃ m : ℕ, 0 < m ∧ m < 19 ∧ 77 ∣ (m + 2) * (m + 3) :=
      ⟨n, hn.1, hlt', hn.2⟩
    -- This statement is false; `decide` can verify it.
    have h_no : ¬ ∃ m : ℕ, 0 < m ∧ m < 19 ∧ 77 ∣ (m + 2) * (m + 3) := by decide
    exact (h_no h_ex).elim
  exact hmin
