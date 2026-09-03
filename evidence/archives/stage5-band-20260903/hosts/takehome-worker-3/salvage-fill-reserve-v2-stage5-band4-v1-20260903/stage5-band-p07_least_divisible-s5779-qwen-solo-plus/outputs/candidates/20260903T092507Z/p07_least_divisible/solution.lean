import Mathlib

/-- The least positive integer `n` such that `77` divides `(n + 2) * (n + 3)`.
Must be a numeric literal. -/
abbrev p07_answer : ℕ := 19

/-- `p07_answer` is the least element of the set of positive `n` with
`77 ∣ (n + 2) * (n + 3)`. -/
theorem p07_least_divisible :
    IsLeast {n : ℕ | 0 < n ∧ 77 ∣ (n + 2) * (n + 3)} p07_answer := by
  constructor
  · -- Part 1: 19 is in the set
    constructor
    · -- 0 < 19
      norm_num
    · -- 77 ∣ (19 + 2) * (19 + 3)
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Part 2: 19 is the least
    intro b hb
    rcases hb with ⟨hb_pos, hb_div⟩
    by_contra h
    have hb_lt_19 : b < 19 := lt_of_not_ge h
    
    -- 77 divides the product implies 7 and 11 divide the product
    have h7 : 7 ∣ (b + 2) * (b + 3) := dvd_trans (by norm_num) hb_div
    have h11 : 11 ∣ (b + 2) * (b + 3) := dvd_trans (by norm_num) hb_div
    
    -- Split cases for 7
    have h7_cases : 7 ∣ b + 2 ∨ 7 ∣ b + 3 := by
      rw [Nat.Prime.dvd_mul (by decide)] at h7
      exact h7
    
    -- Split cases for 11
    have h11_cases : 11 ∣ b + 2 ∨ 11 ∣ b + 3 := by
      rw [Nat.Prime.dvd_mul (by decide)] at h11
      exact h11
    
    -- Analyze cases
    rcases h7_cases with (h7_left | h7_right)
    · -- Case: 7 ∣ b + 2
      rcases h11_cases with (h11_left | h11_right)
      · -- Subcase: 7 ∣ b + 2 and 11 ∣ b + 2
        -- Implies 77 ∣ b + 2, so b + 2 ≥ 77, contradicting b < 19
        have h77 : 77 ∣ b + 2 := by
          have := Nat.lcm_dvd h7_left h11_left
          norm_num at this
          exact this
        have h_b2_ge_77 : 77 ≤ b + 2 := Nat.le_of_dvd (by omega) h77
        omega
      · -- Subcase: 7 ∣ b + 2 and 11 ∣ b + 3
        -- 7 ∣ b + 2 and 11 ∣ b + 3 and b < 19
        have : False := by
          omega
        exact this
    · -- Case: 7 ∣ b + 3
      rcases h11_cases with (h11_left | h11_right)
      · -- Subcase: 7 ∣ b + 3 and 11 ∣ b + 2
        -- 7 ∣ b + 3 and 11 ∣ b + 2 and b < 19
        have : False := by
          omega
        exact this
      · -- Subcase: 7 ∣ b + 3 and 11 ∣ b + 3
        -- Implies 77 ∣ b + 3, so b + 3 ≥ 77, contradicting b < 19
        have h77 : 77 ∣ b + 3 := by
          have := Nat.lcm_dvd h7_right h11_right
          norm_num at this
          exact this
        have h_b3_ge_77 : 77 ≤ b + 3 := Nat.le_of_dvd (by omega) h77
        omega
