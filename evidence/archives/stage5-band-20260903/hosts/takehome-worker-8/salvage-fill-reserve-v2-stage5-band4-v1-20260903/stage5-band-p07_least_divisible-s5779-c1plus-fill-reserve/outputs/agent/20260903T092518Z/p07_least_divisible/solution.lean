import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- First we show that `19` belongs to the set.
  refine ⟨?mem, ?least⟩
  · -- `19` is positive and makes the product divisible by `77`.
    have hpos : (0 : ℕ) < 19 := by decide
    have hdiv : 77 ∣ (19 + 2) * (19 + 3) := by
      -- `(19+2)*(19+3) = 21*22 = 462 = 77*6`
      norm_num
    exact ⟨hpos, hdiv⟩
  · -- Now we prove minimality: any other element of the set is at least `19`.
    intro y hy
    rcases hy with ⟨hypos, hydiv⟩
    by_contra hlt
    -- `hlt : ¬ 19 ≤ y`, hence `y < 19`.
    have hylt : y < 19 := Nat.lt_of_not_ge hlt
    -- The existence of a smaller witness contradicts a decidable check.
    have hno : ¬ ∃ n : ℕ, n < 19 ∧ 77 ∣ (n + 2) * (n + 3) := by decide
    have : ∃ n : ℕ, n < 19 ∧ 77 ∣ (n + 2) * (n + 3) := ⟨y, hylt, hydiv⟩
    exact (hno this).elim
