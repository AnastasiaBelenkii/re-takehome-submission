import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  -- Part 1: Show 19 is in the set
  have h₁ : 0 < 19 := by decide
  have h₂ : 77 ∣ (19 + 2) * (19 + 3) := by
    norm_num [Nat.dvd_iff_mod_eq_zero]
    <;> decide
  
  constructor
  · exact ⟨h₁, h₂⟩
  
  -- Part 2: Show 19 is the least element
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  rcases hn with ⟨hn_pos, hn_dvd⟩
  
  -- Prove 19 ≤ n by contradiction
  by_contra h
  have h_lt : n < 19 := Nat.not_le.mp h
  
  -- Check all cases from 1 to 18
  interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at hn_dvd <;> contradiction
