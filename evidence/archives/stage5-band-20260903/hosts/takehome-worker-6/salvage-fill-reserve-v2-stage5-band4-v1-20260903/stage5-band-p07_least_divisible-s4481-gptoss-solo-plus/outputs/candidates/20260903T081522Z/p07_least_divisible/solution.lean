import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- membership of `p07_answer`
  have hmem : (0 < (p07_answer)) ∧ 77 ∣ (p07_answer + 2) * (p07_answer + 3) := by
    constructor
    · decide
    · refine ⟨6, ?_⟩
      norm_num
  refine ⟨?mem, ?lb⟩
  · -- `p07_answer` belongs to the set
    simpa [p07_answer] using hmem
  · -- lower bound: any element of the set is at least `p07_answer`
    intro n hn
    have : 19 ≤ n := by
      by_contra hlt
      have hlt' : n < 19 := Nat.lt_of_not_ge hlt
      have hle : n ≤ 18 := Nat.le_of_lt_succ hlt'
      have hfalse : ¬ (0 < n ∧ 77 ∣ (n + 2) * (n + 3)) := by
        interval_cases hle
        all_goals decide
      exact hfalse hn
    exact this
