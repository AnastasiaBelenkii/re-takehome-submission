import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Proof Sketch:
    -- 1. Show 19 is positive.
    -- 2. Show 77 divides (19+2)*(19+3) = 21*22 = 462.
    -- 3. Combine these facts to show 19 is in the set.
    have h₁ : 0 < (19 : ℕ) := by decide
    have h₂ : 77 ∣ (19 + 2) * (19 + 3) := by norm_num
    exact ⟨h₁, h₂⟩
  · -- Proof Sketch:
    -- 1. Assume n is in the set (0 < n and 77 | (n+2)(n+3)).
    -- 2. Suppose for contradiction n < 19.
    -- 3. Check all n in 1..18 using interval_cases and norm_num.
    -- 4. Divisibility fails for all such n, yielding a contradiction.
    intro n hn
    have h_pos : 0 < n := hn.1
    have h_dvd : 77 ∣ (n + 2) * (n + 3) := hn.2
    have h_ge : 19 ≤ n := by
      by_contra h_lt
      have h_n_lt_19 : n < 19 := by omega
      interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h_dvd <;> cases h_dvd
    exact h_ge
