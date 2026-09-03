import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- `p07_answer` belongs to the set
    have hpos : (0 : ℕ) < p07_answer := by decide
    have hdiv : 77 ∣ (p07_answer + 2) * (p07_answer + 3) := by
      -- (19+2)*(19+3) = 21*22 = 462 = 77*6
      norm_num
    exact ⟨hpos, hdiv⟩
  · -- minimality: any other element is at least `p07_answer`
    intro m hm
    rcases hm with ⟨hmpos, hmdvd⟩
    by_contra hnot
    have hle : m ≤ 18 := by
      -- from ¬ 19 ≤ m we get m < 19, hence m ≤ 18
      have : m < p07_answer := Nat.not_le.mp hnot
      exact (Nat.lt_succ_iff).mp this
    -- analyse all possibilities for `m` with `m ≤ 18`
    interval_cases hle
    all_goals
      have : ¬ (77 ∣ (m + 2) * (m + 3)) := by
        norm_num
      exact this hmdvd
