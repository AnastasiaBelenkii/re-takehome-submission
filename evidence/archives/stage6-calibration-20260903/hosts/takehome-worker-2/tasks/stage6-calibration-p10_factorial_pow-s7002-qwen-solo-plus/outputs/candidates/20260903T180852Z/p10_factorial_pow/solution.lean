import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- First show that 6 ∈ S by verifying 6! < 3^6
  have h_mem : Nat.factorial 6 < 3 ^ 6 := by decide
  
  -- Show that for all n > 6, n! ≥ 3^n (so they're not in S)
  have h_upper_bound : ∀ n : ℕ, n > 6 → Nat.factorial n ≥ 3 ^ n := by
    intro n hn
    induction' hn with k hk IH
    · -- Base case: n = 7
      norm_num [Nat.factorial, pow_succ]
    · -- Inductive step: n = k + 1, where k > 6
      simp_all [Nat.factorial, pow_succ]
      -- We have IH: Nat.factorial k ≥ 3^k
      -- We want: (k+1) * Nat.factorial k ≥ 3 * 3^k
      -- Since k > 6, k ≥ 7, so k+1 ≥ 8 > 3
      
      have h_k_ge_7 : k ≥ 7 := Nat.succ_le_iff.mpr hk
      have h_k_plus_1_ge_8 : k + 1 ≥ 8 := Nat.add_le_add_right h_k_ge_7 1
      
      calc
        (k + 1) * Nat.factorial k ≥ (k + 1) * 3 ^ k := by
          gcongr
          <;> assumption
        _ ≥ 8 * 3 ^ k := by
          gcongr
          <;> assumption
        _ ≥ 3 * 3 ^ k := by
          have : 8 ≥ 3 := by norm_num
          exact Nat.mul_le_mul_right (3 ^ k) this
        _ = 3 ^ (k + 1) := by rw [pow_succ, mul_comm]
  
  -- Combine to show IsGreatest
  constructor
  · exact h_mem
  · intro n hn
    by_contra h
    have h_gt_6 : n > 6 := Nat.not_le.mp h
    have h_fact_ge_pow : Nat.factorial n ≥ 3 ^ n := h_upper_bound n h_gt_6
    -- hn : n! < 3^n
    -- h_fact_ge_pow : n! ≥ 3^n
    -- Contradiction
    have : 3 ^ n < 3 ^ n := lt_of_le_of_lt h_fact_ge_pow hn
    exact lt_irrefl (3 ^ n) this
