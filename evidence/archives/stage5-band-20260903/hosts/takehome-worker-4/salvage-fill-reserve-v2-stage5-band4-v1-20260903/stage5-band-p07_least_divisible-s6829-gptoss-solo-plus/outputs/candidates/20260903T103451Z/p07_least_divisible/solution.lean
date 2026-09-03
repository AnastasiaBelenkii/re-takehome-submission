import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- First we show that `19` belongs to the set.
  have h_mem : (0 < (19 : ℕ)) ∧ 77 ∣ (19 + 2) * (19 + 3) := by
    constructor
    · decide
    · norm_num
  refine ⟨?left, ?right⟩
  · exact h_mem
  · intro n hn
    -- Existence of a solution (namely `19`) gives a `Nat.find`.
    have h_exists : ∃ m, 0 < m ∧ 77 ∣ (m + 2) * (m + 3) :=
      ⟨19, h_mem.1, h_mem.2⟩
    -- Characterise the `Nat.find` as the smallest such number.
    have h_find_eq : Nat.find h_exists = 19 := by
      -- Use `Nat.find_eq_iff` : the `find` equals `19` iff `19` satisfies the predicate
      -- and no smaller number does.
      apply (Nat.find_eq_iff).2
      constructor
      · -- No smaller positive integer works.
        intro m hm
        -- The statement `¬ (0 < m ∧ 77 ∣ (m + 2) * (m + 3))` is decidable and can be
        -- checked by brute force because `m < 19`.
        have : ¬ (0 < m ∧ 77 ∣ (m + 2) * (m + 3)) := by
          decide
        exact this
      · -- `19` itself works.
        exact h_mem
    -- Minimality of `Nat.find` gives `Nat.find h_exists ≤ n`.
    have h_min : Nat.find h_exists ≤ n := Nat.find_min' h_exists hn
    -- Rewrite `Nat.find h_exists` to `19`.
    simpa [h_find_eq] using h_min
