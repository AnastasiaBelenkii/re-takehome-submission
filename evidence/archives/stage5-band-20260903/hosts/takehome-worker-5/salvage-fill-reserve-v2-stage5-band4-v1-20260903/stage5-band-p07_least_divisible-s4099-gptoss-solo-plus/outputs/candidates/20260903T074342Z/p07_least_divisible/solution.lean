import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- `19` satisfies the condition
  have h19_mem : (0 < (19 : ℕ)) ∧ 77 ∣ (19 + 2) * (19 + 3) := by
    constructor
    · decide
    · have : ((21) * (22)) % 77 = 0 := by norm_num
      exact (Nat.dvd_iff_mod_eq_zero).mpr this
  refine ⟨h19_mem, ?_⟩
  intro n hn
  rcases hn with ⟨hn_pos, hdiv⟩
  -- obtain divisibility by the prime factors
  have h
