import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  refine ⟨?mem, ?least⟩
  · -- `p07_answer` belongs to the set
    have hcalc : (p07_answer + 2) * (p07_answer + 3) = 77 * 6 := by
      norm_num [p07_answer]
    have hdiv : 77 ∣ (p07_answer + 2) * (p07_answer + 3) := by
      refine ⟨6, ?_⟩
      simpa [p07_answer] using hcalc
    exact ⟨by decide, hdiv⟩
  · -- minimality
    intro m hm
    rcases hm with ⟨hmpos, hdiv⟩
    have hle_or := le_or_lt p07_answer m
    cases hle_or with
    | inl hle => exact hle
    | inr hlt =>
        -- `m < 19`, contradicts the divisibility condition
        have hle18 : m ≤ 18 := by
          have : m < 19 := by
            simpa [p07_answer] using hlt
          exact Nat.le_of_lt_succ this
        have hfalse : False := by
          interval_cases m using hle18
          all_goals
            have hnot : ¬ 77 ∣ (m + 2) * (m + 3) := by decide
            exact hnot hdiv
        exact (False.elim hfalse)
