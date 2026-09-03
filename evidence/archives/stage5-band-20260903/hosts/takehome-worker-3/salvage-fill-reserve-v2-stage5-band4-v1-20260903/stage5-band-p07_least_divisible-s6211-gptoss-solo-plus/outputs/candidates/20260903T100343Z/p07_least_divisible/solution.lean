import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`. -/
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
  intro m hm
  rcases hm with ⟨hm_pos, hm_div⟩
  -- prove that any other element is at least `19`
  by_contra hlt
  have hlt' : m < p07_answer := Nat.lt_of_not_ge hlt
  have hneg : ¬ ∃ n, n < p07_answer ∧ 0 < n ∧ 77 ∣ (n + 2) * (n + 3) := by
    decide
  have : ∃ n, n < p07_answer ∧ 0 < n ∧ 77 ∣ (n + 2) * (n + 3) :=
    ⟨m, hlt', hm_pos, hm_div⟩
  exact (hneg this).elim
